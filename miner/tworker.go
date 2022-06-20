package miner

import (
	"bytes"
	"errors"
	"math/big"
	"sync"
	"sync/atomic"
	"time"

	mapset "github.com/deckarep/golang-set"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/misc"
	"github.com/ethereum/go-ethereum/core"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/systemcontracts"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/event"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/trie"
)

type tworker struct {
	prefetcher  core.Prefetcher
	config      *Config
	chainConfig *params.ChainConfig
	engine      consensus.Engine
	eth         Backend
	chain       *core.BlockChain

	current *environment

	mu sync.RWMutex

	snapshotMu    sync.RWMutex
	snapshotBlock *types.Block
	snapshotState *state.StateDB

	chainHeadCh  chan core.ChainHeadEvent
	chainHeadSub event.Subscription
}

func newTWorker(config *Config, chainConfig *params.ChainConfig, engine consensus.Engine, eth Backend) *tworker {
	worker := &tworker{
		prefetcher:  core.NewStatePrefetcher(chainConfig, eth.BlockChain(), engine),
		config:      config,
		chainConfig: chainConfig,
		engine:      engine,
		eth:         eth,
		chain:       eth.BlockChain(),
		chainHeadCh: make(chan core.ChainHeadEvent, chainHeadChanSize),
	}

	// Subscribe events for blockchain
	worker.chainHeadSub = eth.BlockChain().SubscribeChainHeadEvent(worker.chainHeadCh)

	go worker.mainLoop()

	return worker
}

// pending returns the pending state and corresponding block.
func (w *tworker) pending() (*types.Block, *state.StateDB) {
	// return a snapshot to avoid contention on currentMu mutex
	w.snapshotMu.RLock()
	defer w.snapshotMu.RUnlock()
	if w.snapshotState == nil {
		return nil, nil
	}
	return w.snapshotBlock, w.snapshotState.Copy()
}

func (w *tworker) mainLoop() {
	for {
		select {
		case head := <-w.chainHeadCh:
			log.Info("[tworker] receive new head event", "head", head.Block.NumberU64())
			timestamp := time.Now().Unix()
			w.commitNewWork(nil, timestamp)
			w.updateSnapshot()
		}
	}
}

func (w *tworker) commitNewWork(interrupt *int32, timestamp int64) {
	w.mu.RLock()
	defer w.mu.RUnlock()

	parent := w.chain.CurrentBlock()

	if parent.Time() >= uint64(timestamp) {
		timestamp = int64(parent.Time() + 1)
	}
	num := parent.Number()
	header := &types.Header{
		ParentHash: parent.Hash(),
		Number:     num.Add(num, common.Big1),
		GasLimit:   core.CalcGasLimit(parent, w.config.GasFloor, w.config.GasCeil),
		Extra:      []byte{},
		Time:       uint64(timestamp),
	}
	// Only set the coinbase if our consensus engine is running (avoid spurious block rewards)
	if err := w.engine.Prepare(w.chain, header); err != nil {
		log.Error("[tworker] Failed to prepare header for mining", "err", err)
		return
	}
	// If we are care about TheDAO hard-fork check whether to override the extra-data or not
	if daoBlock := w.chainConfig.DAOForkBlock; daoBlock != nil {
		// Check whether the block is among the fork extra-override range
		limit := new(big.Int).Add(daoBlock, params.DAOForkExtraRange)
		if header.Number.Cmp(daoBlock) >= 0 && header.Number.Cmp(limit) < 0 {
			// Depending whether we support or oppose the fork, override differently
			if w.chainConfig.DAOForkSupport {
				header.Extra = common.CopyBytes(params.DAOForkBlockExtra)
			} else if bytes.Equal(header.Extra, params.DAOForkBlockExtra) {
				header.Extra = []byte{} // If miner opposes, don't let it use the reserved extra-data
			}
		}
	}
	// Could potentially happen if starting to mine in an odd state.
	err := w.makeCurrent(parent, header)
	if err != nil {
		log.Error("[tworker] Failed to create mining context", "err", err)
		return
	}
	// Create the current work task and check any fork transitions needed
	env := w.current
	if w.chainConfig.DAOForkSupport && w.chainConfig.DAOForkBlock != nil && w.chainConfig.DAOForkBlock.Cmp(header.Number) == 0 {
		misc.ApplyDAOHardFork(env.state)
	}
	systemcontracts.UpgradeBuildInSystemContract(w.chainConfig, header.Number, env.state)

	// Fill the block with all available pending transactions.
	pending, err := w.eth.TxPool().Pending()
	if err != nil {
		log.Error("[tworker] Failed to fetch pending transactions", "err", err)
	}
	// Short circuit if there is no available pending transactions
	if len(pending) != 0 {
		start := time.Now()
		// Split the pending transactions into locals and remotes
		localTxs, remoteTxs := make(map[common.Address]types.Transactions), pending
		for _, account := range w.eth.TxPool().Locals() {
			if txs := remoteTxs[account]; len(txs) > 0 {
				delete(remoteTxs, account)
				localTxs[account] = txs
			}
		}
		if len(localTxs) > 0 {
			txs := types.NewTransactionsByPriceAndNonce(w.current.signer, localTxs)
			if w.commitTransactions(txs, interrupt) {
				return
			}
		}
		if len(remoteTxs) > 0 {
			txs := types.NewTransactionsByPriceAndNonce(w.current.signer, remoteTxs)
			if w.commitTransactions(txs, interrupt) {
				return
			}
		}
		// commitTxsTimer.UpdateSince(start)
		log.Info("[tworker] Gas pool", "height", header.Number.String(), "pool", w.current.gasPool.String(), "start: ", start)
	}
}

// makeCurrent creates a new environment for the current cycle.
func (w *tworker) makeCurrent(parent *types.Block, header *types.Header) error {
	// Retrieve the parent state to execute on top and start a prefetcher for
	// the miner to speed block sealing up a bit
	state, err := w.chain.StateAtWithSharedPool(parent.Root())
	if err != nil {
		return err
	}
	state.StartPrefetcher("miner")

	env := &environment{
		signer:    types.MakeSigner(w.chainConfig, header.Number),
		state:     state,
		ancestors: mapset.NewSet(),
		family:    mapset.NewSet(),
		uncles:    mapset.NewSet(),
		header:    header,
	}
	// Keep track of transactions which return errors so they can be removed
	env.tcount = 0

	// Swap out the old work with the new one, terminating any leftover prefetcher
	// processes in the mean time and starting a new one.
	if w.current != nil && w.current.state != nil {
		w.current.state.StopPrefetcher()
	}
	w.current = env
	return nil
}

func (w *tworker) commitTransactions(txs *types.TransactionsByPriceAndNonce, interrupt *int32) bool {
	// Short circuit if current is nil
	if w.current == nil {
		return true
	}

	if w.current.gasPool == nil {
		w.current.gasPool = new(core.GasPool).AddGas(w.current.header.GasLimit)
		if w.chain.Config().IsEuler(w.current.header.Number) {
			w.current.gasPool.SubGas(params.SystemTxsGas * 3)
		} else {
			w.current.gasPool.SubGas(params.SystemTxsGas)
		}

	}

	var coalescedLogs []*types.Log
	var stopTimer *time.Timer
	delay := w.engine.Delay(w.chain, w.current.header)
	if delay != nil {
		stopTimer = time.NewTimer(*delay - w.config.DelayLeftOver)
		log.Info("[tworker] Time left for mining work", "left", (*delay - w.config.DelayLeftOver).String(), "leftover", w.config.DelayLeftOver)
		defer stopTimer.Stop()
	}

	// initilise bloom processors
	processorCapacity := 100
	if txs.CurrentSize() < processorCapacity {
		processorCapacity = txs.CurrentSize()
	}
	bloomProcessors := core.NewAsyncReceiptBloomGenerator(processorCapacity)

	interruptCh := make(chan struct{})
	defer close(interruptCh)
	//prefetch txs from all pending txs
	txsPrefetch := txs.Copy()
	tx := txsPrefetch.Peek()
	txCurr := &tx
	w.prefetcher.PrefetchMining(txsPrefetch, w.current.header, w.current.gasPool.Gas(), w.current.state.Copy(), *w.chain.GetVMConfig(), interruptCh, txCurr)

LOOP:
	for {
		// In the following three cases, we will interrupt the execution of the transaction.
		// (1) new head block event arrival, the interrupt signal is 1
		// (2) worker start or restart, the interrupt signal is 1
		// (3) worker recreate the mining block with any newly arrived transactions, the interrupt signal is 2.
		// For the first two cases, the semi-finished work will be discarded.
		// For the third case, the semi-finished work will be submitted to the consensus engine.
		if interrupt != nil && atomic.LoadInt32(interrupt) != commitInterruptNone {
			return atomic.LoadInt32(interrupt) == commitInterruptNewHead
		}
		// If we don't have enough gas for any further transactions then we're done
		if w.current.gasPool.Gas() < params.TxGas {
			log.Trace("[tworker] Not enough gas for further transactions", "have", w.current.gasPool, "want", params.TxGas)
			break
		}
		if stopTimer != nil {
			select {
			case <-stopTimer.C:
				log.Info("[tworker] Not enough time for further transactions", "txs", len(w.current.txs))
				break LOOP
			default:
			}
		}
		// Retrieve the next transaction and abort if all done
		tx = txs.Peek()
		if tx == nil {
			break
		}
		// Error may be ignored here. The error has already been checked
		// during transaction acceptance is the transaction pool.
		//
		// We use the eip155 signer regardless of the current hf.
		//from, _ := types.Sender(w.current.signer, tx)
		// Check whether the tx is replay protected. If we're not in the EIP155 hf
		// phase, start ignoring the sender until we do.
		if tx.Protected() && !w.chainConfig.IsEIP155(w.current.header.Number) {
			//log.Trace("Ignoring reply protected transaction", "hash", tx.Hash(), "eip155", w.chainConfig.EIP155Block)
			txs.Pop()
			continue
		}
		// Start executing the transaction
		w.current.state.Prepare(tx.Hash(), common.Hash{}, w.current.tcount)

		logs, err := w.commitTransaction(tx, bloomProcessors)
		switch {
		case errors.Is(err, core.ErrGasLimitReached):
			// Pop the current out-of-gas transaction without shifting in the next from the account
			//log.Trace("Gas limit exceeded for current block", "sender", from)
			txs.Pop()

		case errors.Is(err, core.ErrNonceTooLow):
			// New head notification data race between the transaction pool and miner, shift
			//log.Trace("Skipping transaction with low nonce", "sender", from, "nonce", tx.Nonce())
			txs.Shift()

		case errors.Is(err, core.ErrNonceTooHigh):
			// Reorg notification data race between the transaction pool and miner, skip account =
			//log.Trace("Skipping account with hight nonce", "sender", from, "nonce", tx.Nonce())
			txs.Pop()

		case errors.Is(err, nil):
			// Everything ok, collect the logs and shift in the next transaction from the same account
			coalescedLogs = append(coalescedLogs, logs...)
			w.current.tcount++
			txs.Shift()

		case errors.Is(err, core.ErrTxTypeNotSupported):
			// Pop the unsupported transaction without shifting in the next from the account
			//log.Trace("Skipping unsupported transaction type", "sender", from, "type", tx.Type())
			txs.Pop()

		default:
			// Strange error, discard the transaction and get the next in line (note, the
			// nonce-too-high clause will prevent us from executing in vain).
			//log.Debug("Transaction failed, account skipped", "hash", tx.Hash(), "err", err)
			txs.Shift()
		}
	}
	bloomProcessors.Close()

	// Notify resubmit loop to decrease resubmitting interval if current interval is larger
	// than the user-specified one.
	return false
}

func (w *tworker) commitTransaction(tx *types.Transaction, receiptProcessors ...core.ReceiptProcessor) ([]*types.Log, error) {
	snap := w.current.state.Snapshot()

	receipt, err := core.ApplyTransaction(w.chainConfig, w.chain, nil, w.current.gasPool, w.current.state, w.current.header, tx, &w.current.header.GasUsed, *w.chain.GetVMConfig(), receiptProcessors...)
	if err != nil {
		w.current.state.RevertToSnapshot(snap)
		return nil, err
	}
	w.current.txs = append(w.current.txs, tx)
	w.current.receipts = append(w.current.receipts, receipt)

	return receipt.Logs, nil
}

func (w *tworker) updateSnapshot() {
	w.snapshotMu.Lock()
	defer w.snapshotMu.Unlock()

	w.snapshotBlock = types.NewBlock(
		w.current.header,
		w.current.txs,
		[]*types.Header{},
		w.current.receipts,
		trie.NewStackTrie(nil),
	)
	w.snapshotState = w.current.state.Copy()
}
