import Beacon.Block

/-!
# Incremental roots for the large state vectors

`process_slot` needs the state root at every slot. Four state vectors
(`block_roots`, `state_roots`, `randao_mixes`, `slashings`) hold most of the
chunks and change in one or two places per slot. A `TreeCache` keeps every
layer of a vector's Merkle tree; `refresh` finds the chunks that differ from
the cached leaves and rehashes only their paths (or rebuilds when many
changed).

Status: tested, not proved. `cachedStateRoot` is compared with
`BeaconState.codec.root` by the vector runner on every transition case, and
the incremental path is exercised by the `sanity` vectors, whose expected
post-states contain the cached roots.
-/

namespace Beacon

structure TreeCache where
  /-- `layers[0]` is the leaf chunks; `layers[k + 1]` hashes pairs of
      `layers[k]`; the last layer is the root of a `depth`-level tree. -/
  layers : Array ByteArray := #[]

def TreeCache.buildLoop (depth : Nat) : Nat → Array ByteArray → Array ByteArray
  | 0, layers => layers
  | fuel + 1, layers =>
    TreeCache.buildLoop depth fuel (layers.push (hashLayer layers.back! (depth - (fuel + 1))))

def TreeCache.build (leaves : ByteArray) (depth : Nat) : TreeCache :=
  ⟨TreeCache.buildLoop depth depth #[leaves]⟩

def TreeCache.root (c : TreeCache) : ByteArray := c.layers.back!

def chunkEq (a b : ByteArray) (offset : Nat) : Bool :=
  Nat.all 32 fun j _ => a.get! (offset + j) == b.get! (offset + j)

/-- Indices of the 32-byte chunks in which `a` and `b` (equal sizes)
    differ, ascending. -/
def changedChunks (a b : ByteArray) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:a.size / 32] do
    if !chunkEq a b (32 * i) then out := out.push i
  return out

/-- Parents of ascending child indices, ascending and without repeats. -/
def parentIndices (children : Array Nat) : Array Nat :=
  children.foldl (fun acc i => if acc.back? == some (i / 2) then acc else acc.push (i / 2)) #[]

/-- Rehash the parents of the dirty chunks of layer `k` into layer `k + 1`. -/
def TreeCache.rehash (layers : Array ByteArray) (k : Nat) (dirty : Array Nat) : Array ByteArray × Array Nat :=
  let below := layers[k]!
  let parents := parentIndices dirty
  let above := parents.foldl
    (fun above j =>
      let left := below.extract (64 * j) (64 * j + 32)
      let right := if 64 * j + 64 ≤ below.size then below.extract (64 * j + 32) (64 * j + 64) else zeroHashes[k]!
      (sha (left ++ right)).copySlice 0 above (32 * j) 32)
    layers[k + 1]!
  (layers.set! (k + 1) above, parents)

def TreeCache.updateLoop (depth : Nat) : Nat → Array ByteArray → Array Nat → Array ByteArray
  | 0, layers, _ => layers
  | fuel + 1, layers, dirty =>
    let (layers, parents) := TreeCache.rehash layers (depth - (fuel + 1)) dirty
    TreeCache.updateLoop depth fuel layers parents

/-- A cache for `leaves`: the old cache when nothing changed, an update of
    the dirty paths when few chunks changed, a rebuild otherwise. -/
def TreeCache.refresh (c : TreeCache) (leaves : ByteArray) (depth : Nat) : TreeCache :=
  if c.layers.size != depth + 1 || c.layers[0]!.size != leaves.size || leaves.size == 0 then
    TreeCache.build leaves depth
  else
    let dirty := changedChunks c.layers[0]! leaves
    if dirty.size == 0 then c
    else if dirty.size * 8 > leaves.size / 32 then TreeCache.build leaves depth
    else ⟨TreeCache.updateLoop depth depth (c.layers.set! 0 leaves) dirty⟩

structure HashCache where
  blockRoots : TreeCache := {}
  stateRoots : TreeCache := {}
  randaoMixes : TreeCache := {}
  slashings : TreeCache := {}

/-- `hash_tree_root(state)` with the four large vectors taken from the
    cache. The field list must match `BeaconState` in `Beacon/Types.lean`. -/
def cachedStateRoot (p : Preset) (s : BeaconState) (cache : HashCache) : ByteArray × HashCache :=
  let u := Codec.u64
  let cp := Checkpoint.codec
  let reg (_ : Preset) : Nat := validatorRegistryLimit
  let blockRoots := cache.blockRoots.refresh (Codec.concatMap id s.blockRoots) (log2ceil p.slotsPerHistoricalRoot)
  let stateRoots := cache.stateRoots.refresh (Codec.concatMap id s.stateRoots) (log2ceil p.slotsPerHistoricalRoot)
  let randaoMixes := cache.randaoMixes.refresh (Codec.concatMap id s.randaoMixes) (log2ceil p.epochsPerHistoricalVector)
  let slashings := cache.slashings.refresh (padTo32 (Codec.concatMap (u.encode p) s.slashings))
    (log2ceil ((p.epochsPerSlashingsVector * 8 + 31) / 32))
  let roots : List ByteArray := [
    u.root p s.genesisTime,
    Codec.bytes32.root p s.genesisValidatorsRoot,
    u.root p s.slot,
    Fork.codec.root p s.fork,
    BeaconBlockHeader.codec.root p s.latestBlockHeader,
    blockRoots.root,
    stateRoots.root,
    (Codec.list Codec.bytes32 (fun _ => historicalRootsLimit)).root p s.historicalRoots,
    Eth1Data.codec.root p s.eth1Data,
    (Codec.list Eth1Data.codec (fun p => p.epochsPerEth1VotingPeriod * p.slotsPerEpoch)).root p s.eth1DataVotes,
    u.root p s.eth1DepositIndex,
    (Codec.list Validator.codec reg).root p s.validators,
    (Codec.list u reg).root p s.balances,
    randaoMixes.root,
    slashings.root,
    (Codec.byteList reg).root p s.previousEpochParticipation,
    (Codec.byteList reg).root p s.currentEpochParticipation,
    (Codec.bitvector (fun _ => justificationBitsLength)).root p s.justificationBits,
    cp.root p s.previousJustifiedCheckpoint,
    cp.root p s.currentJustifiedCheckpoint,
    cp.root p s.finalizedCheckpoint,
    (Codec.list u reg).root p s.inactivityScores,
    SyncCommittee.codec.root p s.currentSyncCommittee,
    SyncCommittee.codec.root p s.nextSyncCommittee,
    ExecutionPayloadHeader.codec.root p s.latestExecutionPayloadHeader,
    u.root p s.nextWithdrawalIndex,
    u.root p s.nextWithdrawalValidatorIndex,
    (Codec.list HistoricalSummary.codec (fun _ => historicalRootsLimit)).root p s.historicalSummaries,
    u.root p s.depositRequestsStartIndex,
    u.root p s.depositBalanceToConsume,
    u.root p s.exitBalanceToConsume,
    u.root p s.earliestExitEpoch,
    u.root p s.consolidationBalanceToConsume,
    u.root p s.earliestConsolidationEpoch,
    (Codec.list PendingDeposit.codec (fun _ => pendingDepositsLimit)).root p s.pendingDeposits,
    (Codec.list PendingPartialWithdrawal.codec (fun p => p.pendingPartialWithdrawalsLimit)).root p s.pendingPartialWithdrawals,
    (Codec.list PendingConsolidation.codec (fun p => p.pendingConsolidationsLimit)).root p s.pendingConsolidations,
    (Codec.vec u (fun p => (minSeedLookahead + 1) * p.slotsPerEpoch)).root p s.proposerLookahead]
  (Codec.containerRoot roots, { blockRoots, stateRoots, randaoMixes, slashings })

end Beacon
