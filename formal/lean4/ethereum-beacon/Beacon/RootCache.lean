import Beacon.Block

/-!
# Incremental roots for the large state fields

`process_slot` needs the state root at every slot. Nine state fields hold
almost all of the chunks: `block_roots`, `state_roots`, `randao_mixes`,
`slashings`, `validators`, `balances`, the two participation lists and
`inactivity_scores`. A `TreeCache` keeps every layer of a field's Merkle
tree; `refresh` finds the chunks that differ from the cached leaves (or
were appended) and rehashes only their paths, or rebuilds when many
changed. The registry cache also keeps each validator's own root and
recomputes it only for validators that differ from the cached copy.

Cost per slot: one comparison pass over the cached leaves (linear in the
registry, no hashing) plus `depth` hashes per changed chunk.

Status: tested, not proved. `cachedStateRoot` from an empty cache is
compared with `BeaconState.codec.root` by the vector runner on every
transition case, and the incremental path is exercised by the `sanity`
vectors, whose expected post-states and block state roots contain the
cached roots.
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

def TreeCache.root (c : TreeCache) (depth : Nat) : ByteArray :=
  if c.layers.size != depth + 1 || c.layers[0]!.size == 0 then zeroHashes[depth]! else c.layers.back!

def chunkEq (a b : ByteArray) (offset : Nat) : Bool :=
  Nat.all 32 fun j _ => a.get! (offset + j) == b.get! (offset + j)

/-- Indices of the 32-byte chunks of `b` that differ from `a` or lie
    beyond its end, ascending. -/
def changedChunks (a b : ByteArray) : Array Nat := Id.run do
  let mut out := #[]
  let common := min a.size b.size / 32
  for i in [0:common] do
    if !chunkEq a b (32 * i) then out := out.push i
  for i in [common:b.size / 32] do
    out := out.push i
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

/-- A cache for `leaves`, given the indices of the chunks that changed or
    were appended since `c` (ascending): an update of the dirty paths when
    the tree has the same depth, did not shrink and few chunks changed; a
    rebuild otherwise. -/
def TreeCache.updateWith (c : TreeCache) (leaves : ByteArray) (depth : Nat) (dirty : Array Nat) : TreeCache :=
  if c.layers.size != depth + 1 || leaves.size < c.layers[0]!.size || c.layers[0]!.size == 0 then
    TreeCache.build leaves depth
  else if dirty.size == 0 then c
  else if dirty.size * 8 > leaves.size / 32 then TreeCache.build leaves depth
  else ⟨TreeCache.updateLoop depth depth (c.layers.set! 0 leaves) dirty⟩

/-- A cache for `leaves`, finding the changed chunks by comparison. -/
def TreeCache.refresh (c : TreeCache) (leaves : ByteArray) (depth : Nat) : TreeCache :=
  if c.layers.size != depth + 1 || leaves.size < c.layers[0]!.size || c.layers[0]!.size == 0 then
    TreeCache.build leaves depth
  else c.updateWith leaves depth (changedChunks c.layers[0]! leaves)

/-- Depth of the registry-sized lists of composite elements. -/
def registryDepth : Nat := log2ceil validatorRegistryLimit

structure RegistryCache where
  /-- The registry the roots below were computed from. -/
  validators : Array Validator := #[]
  /-- Each validator's `hash_tree_root`, 32 bytes per validator. -/
  roots : ByteArray := ByteArray.empty
  tree : TreeCache := {}

/-- Recompute the roots of the validators that differ from the cached
    registry or were appended, then update the tree along their paths. -/
def RegistryCache.refresh (p : Preset) (c : RegistryCache) (validators : Array Validator) : RegistryCache :=
  if c.validators.size == 0 || validators.size < c.validators.size then
    let roots := Codec.concatMap (Validator.codec.root p) validators
    ⟨validators, roots, TreeCache.build roots registryDepth⟩
  else
    let (roots, dirty) := Id.run do
      let mut roots := c.roots
      let mut dirty : Array Nat := #[]
      for i in [0:validators.size] do
        if i ≥ c.validators.size || validators[i]! != c.validators[i]! then
          roots := (Validator.codec.root p validators[i]!).copySlice 0 roots (32 * i) 32
          dirty := dirty.push i
      return (roots, dirty)
    ⟨validators, roots, c.tree.updateWith roots registryDepth dirty⟩

structure HashCache where
  blockRoots : TreeCache := {}
  stateRoots : TreeCache := {}
  randaoMixes : TreeCache := {}
  slashings : TreeCache := {}
  registry : RegistryCache := {}
  balances : TreeCache := {}
  inactivityScores : TreeCache := {}
  previousParticipation : TreeCache := {}
  currentParticipation : TreeCache := {}

/-- `hash_tree_root(state)` with the nine large fields taken from the
    cache. The field list must match `BeaconState` in `Beacon/Types.lean`. -/
def cachedStateRoot (p : Preset) (s : BeaconState) (cache : HashCache) : ByteArray × HashCache :=
  let u := Codec.u64
  let cp := Checkpoint.codec
  let blockRoots := cache.blockRoots.refresh (Codec.concatMap id s.blockRoots) (log2ceil p.slotsPerHistoricalRoot)
  let stateRoots := cache.stateRoots.refresh (Codec.concatMap id s.stateRoots) (log2ceil p.slotsPerHistoricalRoot)
  let randaoMixes := cache.randaoMixes.refresh (Codec.concatMap id s.randaoMixes) (log2ceil p.epochsPerHistoricalVector)
  let slashings := cache.slashings.refresh (padTo32 (Codec.concatMap (u.encode p) s.slashings))
    (log2ceil ((p.epochsPerSlashingsVector * 8 + 31) / 32))
  let registry := cache.registry.refresh p s.validators
  let u64Depth := log2ceil ((validatorRegistryLimit * 8 + 31) / 32)
  let u8Depth := log2ceil ((validatorRegistryLimit + 31) / 32)
  let balances := cache.balances.refresh (padTo32 (Codec.concatMap (u.encode p) s.balances)) u64Depth
  let inactivityScores := cache.inactivityScores.refresh
    (padTo32 (Codec.concatMap (u.encode p) s.inactivityScores)) u64Depth
  let previousParticipation := cache.previousParticipation.refresh (padTo32 s.previousEpochParticipation) u8Depth
  let currentParticipation := cache.currentParticipation.refresh (padTo32 s.currentEpochParticipation) u8Depth
  let roots : List ByteArray := [
    u.root p s.genesisTime,
    Codec.bytes32.root p s.genesisValidatorsRoot,
    u.root p s.slot,
    Fork.codec.root p s.fork,
    BeaconBlockHeader.codec.root p s.latestBlockHeader,
    blockRoots.root (log2ceil p.slotsPerHistoricalRoot),
    stateRoots.root (log2ceil p.slotsPerHistoricalRoot),
    (Codec.list Codec.bytes32 (fun _ => historicalRootsLimit)).root p s.historicalRoots,
    Eth1Data.codec.root p s.eth1Data,
    (Codec.list Eth1Data.codec (fun p => p.epochsPerEth1VotingPeriod * p.slotsPerEpoch)).root p s.eth1DataVotes,
    u.root p s.eth1DepositIndex,
    mixInLength (registry.tree.root registryDepth) s.validators.size,
    mixInLength (balances.root u64Depth) s.balances.size,
    randaoMixes.root (log2ceil p.epochsPerHistoricalVector),
    slashings.root (log2ceil ((p.epochsPerSlashingsVector * 8 + 31) / 32)),
    mixInLength (previousParticipation.root u8Depth) s.previousEpochParticipation.size,
    mixInLength (currentParticipation.root u8Depth) s.currentEpochParticipation.size,
    (Codec.bitvector (fun _ => justificationBitsLength)).root p s.justificationBits,
    cp.root p s.previousJustifiedCheckpoint,
    cp.root p s.currentJustifiedCheckpoint,
    cp.root p s.finalizedCheckpoint,
    mixInLength (inactivityScores.root u64Depth) s.inactivityScores.size,
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
  (Codec.containerRoot roots,
    { blockRoots, stateRoots, randaoMixes, slashings, registry, balances, inactivityScores,
      previousParticipation, currentParticipation })

end Beacon
