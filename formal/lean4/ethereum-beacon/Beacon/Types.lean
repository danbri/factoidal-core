import Beacon.SSZ

/-!
# Beacon chain containers (Fulu)

Every container of the Fulu fork that the official `ssz_static` vectors
cover, with field order and types taken from the container definitions in
consensus-specs v1.6.1 (`specs/{phase0,altair,bellatrix,capella,deneb,
electra,fulu}`). `uint64` fields are `Nat`; byte vectors and byte lists are
`ByteArray`; `List[uint8, N]` participation flags are a `ByteArray`.
-/

namespace Beacon
open Codec

def bytes4 : Codec ByteArray := bytesN 4
def bytes20 : Codec ByteArray := bytesN 20
def bytes48 : Codec ByteArray := bytesN 48
def bytes96 : Codec ByteArray := bytesN 96

ssz_container Fork where
  previousVersion : ByteArray := bytes4,
  currentVersion : ByteArray := bytes4,
  epoch : Nat := u64

ssz_container ForkData where
  currentVersion : ByteArray := bytes4,
  genesisValidatorsRoot : ByteArray := bytes32

ssz_container Checkpoint where
  epoch : Nat := u64,
  root : ByteArray := bytes32

ssz_container Validator where
  pubkey : ByteArray := bytes48,
  withdrawalCredentials : ByteArray := bytes32,
  effectiveBalance : Nat := u64,
  slashed : Bool := bool,
  activationEligibilityEpoch : Nat := u64,
  activationEpoch : Nat := u64,
  exitEpoch : Nat := u64,
  withdrawableEpoch : Nat := u64

ssz_container AttestationData where
  slot : Nat := u64,
  index : Nat := u64,
  beaconBlockRoot : ByteArray := bytes32,
  source : Checkpoint := Checkpoint.codec,
  target : Checkpoint := Checkpoint.codec

ssz_container IndexedAttestation where
  attestingIndices : Array Nat := list u64 (fun p => p.maxValidatorsPerCommittee * p.maxCommitteesPerSlot),
  data : AttestationData := AttestationData.codec,
  signature : ByteArray := bytes96

ssz_container PendingAttestation where
  aggregationBits : Array Bool := bitlist (fun p => p.maxValidatorsPerCommittee),
  data : AttestationData := AttestationData.codec,
  inclusionDelay : Nat := u64,
  proposerIndex : Nat := u64

ssz_container Eth1Data where
  depositRoot : ByteArray := bytes32,
  depositCount : Nat := u64,
  blockHash : ByteArray := bytes32

ssz_container HistoricalBatch where
  blockRoots : Array ByteArray := vec bytes32 (fun p => p.slotsPerHistoricalRoot),
  stateRoots : Array ByteArray := vec bytes32 (fun p => p.slotsPerHistoricalRoot)

ssz_container DepositMessage where
  pubkey : ByteArray := bytes48,
  withdrawalCredentials : ByteArray := bytes32,
  amount : Nat := u64

ssz_container DepositData where
  pubkey : ByteArray := bytes48,
  withdrawalCredentials : ByteArray := bytes32,
  amount : Nat := u64,
  signature : ByteArray := bytes96

ssz_container BeaconBlockHeader where
  slot : Nat := u64,
  proposerIndex : Nat := u64,
  parentRoot : ByteArray := bytes32,
  stateRoot : ByteArray := bytes32,
  bodyRoot : ByteArray := bytes32

ssz_container SigningData where
  objectRoot : ByteArray := bytes32,
  domain : ByteArray := bytes32

ssz_container SignedBeaconBlockHeader where
  message : BeaconBlockHeader := BeaconBlockHeader.codec,
  signature : ByteArray := bytes96

ssz_container ProposerSlashing where
  signedHeader1 : SignedBeaconBlockHeader := SignedBeaconBlockHeader.codec,
  signedHeader2 : SignedBeaconBlockHeader := SignedBeaconBlockHeader.codec

ssz_container AttesterSlashing where
  attestation1 : IndexedAttestation := IndexedAttestation.codec,
  attestation2 : IndexedAttestation := IndexedAttestation.codec

ssz_container Attestation where
  aggregationBits : Array Bool := bitlist (fun p => p.maxValidatorsPerCommittee * p.maxCommitteesPerSlot),
  data : AttestationData := AttestationData.codec,
  signature : ByteArray := bytes96,
  committeeBits : Array Bool := bitvector (fun p => p.maxCommitteesPerSlot)

ssz_container SingleAttestation where
  committeeIndex : Nat := u64,
  attesterIndex : Nat := u64,
  data : AttestationData := AttestationData.codec,
  signature : ByteArray := bytes96

ssz_container Deposit where
  proof : Array ByteArray := vec bytes32 (fun _ => depositContractTreeDepth + 1),
  data : DepositData := DepositData.codec

ssz_container VoluntaryExit where
  epoch : Nat := u64,
  validatorIndex : Nat := u64

ssz_container SignedVoluntaryExit where
  message : VoluntaryExit := VoluntaryExit.codec,
  signature : ByteArray := bytes96

ssz_container SyncAggregate where
  syncCommitteeBits : Array Bool := bitvector (fun p => p.syncCommitteeSize),
  syncCommitteeSignature : ByteArray := bytes96

ssz_container SyncCommittee where
  pubkeys : Array ByteArray := vec bytes48 (fun p => p.syncCommitteeSize),
  aggregatePubkey : ByteArray := bytes48

ssz_container Withdrawal where
  index : Nat := u64,
  validatorIndex : Nat := u64,
  address : ByteArray := bytes20,
  amount : Nat := u64

ssz_container ExecutionPayload where
  parentHash : ByteArray := bytes32,
  feeRecipient : ByteArray := bytes20,
  stateRoot : ByteArray := bytes32,
  receiptsRoot : ByteArray := bytes32,
  logsBloom : ByteArray := bytesN bytesPerLogsBloom,
  prevRandao : ByteArray := bytes32,
  blockNumber : Nat := u64,
  gasLimit : Nat := u64,
  gasUsed : Nat := u64,
  timestamp : Nat := u64,
  extraData : ByteArray := byteList (fun _ => maxExtraDataBytes),
  baseFeePerGas : Nat := u256,
  blockHash : ByteArray := bytes32,
  transactions : Array ByteArray := list (byteList (fun _ => maxBytesPerTransaction)) (fun _ => maxTransactionsPerPayload),
  withdrawals : Array Withdrawal := list Withdrawal.codec (fun p => p.maxWithdrawalsPerPayload),
  blobGasUsed : Nat := u64,
  excessBlobGas : Nat := u64

ssz_container ExecutionPayloadHeader where
  parentHash : ByteArray := bytes32,
  feeRecipient : ByteArray := bytes20,
  stateRoot : ByteArray := bytes32,
  receiptsRoot : ByteArray := bytes32,
  logsBloom : ByteArray := bytesN bytesPerLogsBloom,
  prevRandao : ByteArray := bytes32,
  blockNumber : Nat := u64,
  gasLimit : Nat := u64,
  gasUsed : Nat := u64,
  timestamp : Nat := u64,
  extraData : ByteArray := byteList (fun _ => maxExtraDataBytes),
  baseFeePerGas : Nat := u256,
  blockHash : ByteArray := bytes32,
  transactionsRoot : ByteArray := bytes32,
  withdrawalsRoot : ByteArray := bytes32,
  blobGasUsed : Nat := u64,
  excessBlobGas : Nat := u64

ssz_container BLSToExecutionChange where
  validatorIndex : Nat := u64,
  fromBlsPubkey : ByteArray := bytes48,
  toExecutionAddress : ByteArray := bytes20

ssz_container SignedBLSToExecutionChange where
  message : BLSToExecutionChange := BLSToExecutionChange.codec,
  signature : ByteArray := bytes96

ssz_container HistoricalSummary where
  blockSummaryRoot : ByteArray := bytes32,
  stateSummaryRoot : ByteArray := bytes32

ssz_container PendingDeposit where
  pubkey : ByteArray := bytes48,
  withdrawalCredentials : ByteArray := bytes32,
  amount : Nat := u64,
  signature : ByteArray := bytes96,
  slot : Nat := u64

ssz_container PendingPartialWithdrawal where
  validatorIndex : Nat := u64,
  amount : Nat := u64,
  withdrawableEpoch : Nat := u64

ssz_container PendingConsolidation where
  sourceIndex : Nat := u64,
  targetIndex : Nat := u64

ssz_container DepositRequest where
  pubkey : ByteArray := bytes48,
  withdrawalCredentials : ByteArray := bytes32,
  amount : Nat := u64,
  signature : ByteArray := bytes96,
  index : Nat := u64

ssz_container WithdrawalRequest where
  sourceAddress : ByteArray := bytes20,
  validatorPubkey : ByteArray := bytes48,
  amount : Nat := u64

ssz_container ConsolidationRequest where
  sourceAddress : ByteArray := bytes20,
  sourcePubkey : ByteArray := bytes48,
  targetPubkey : ByteArray := bytes48

ssz_container ExecutionRequests where
  deposits : Array DepositRequest := list DepositRequest.codec (fun _ => maxDepositRequestsPerPayload),
  withdrawals : Array WithdrawalRequest := list WithdrawalRequest.codec (fun _ => maxWithdrawalRequestsPerPayload),
  consolidations : Array ConsolidationRequest := list ConsolidationRequest.codec (fun _ => maxConsolidationRequestsPerPayload)

ssz_container BeaconBlockBody where
  randaoReveal : ByteArray := bytes96,
  eth1Data : Eth1Data := Eth1Data.codec,
  graffiti : ByteArray := bytes32,
  proposerSlashings : Array ProposerSlashing := list ProposerSlashing.codec (fun _ => maxProposerSlashings),
  attesterSlashings : Array AttesterSlashing := list AttesterSlashing.codec (fun _ => maxAttesterSlashingsElectra),
  attestations : Array Attestation := list Attestation.codec (fun _ => maxAttestationsElectra),
  deposits : Array Deposit := list Deposit.codec (fun _ => maxDeposits),
  voluntaryExits : Array SignedVoluntaryExit := list SignedVoluntaryExit.codec (fun _ => maxVoluntaryExits),
  syncAggregate : SyncAggregate := SyncAggregate.codec,
  executionPayload : ExecutionPayload := ExecutionPayload.codec,
  blsToExecutionChanges : Array SignedBLSToExecutionChange := list SignedBLSToExecutionChange.codec (fun _ => maxBlsToExecutionChanges),
  blobKzgCommitments : Array ByteArray := list bytes48 (fun _ => maxBlobCommitmentsPerBlock),
  executionRequests : ExecutionRequests := ExecutionRequests.codec

ssz_container BeaconBlock where
  slot : Nat := u64,
  proposerIndex : Nat := u64,
  parentRoot : ByteArray := bytes32,
  stateRoot : ByteArray := bytes32,
  body : BeaconBlockBody := BeaconBlockBody.codec

ssz_container SignedBeaconBlock where
  message : BeaconBlock := BeaconBlock.codec,
  signature : ByteArray := bytes96

ssz_container BeaconState where
  genesisTime : Nat := u64,
  genesisValidatorsRoot : ByteArray := bytes32,
  slot : Nat := u64,
  fork : Fork := Fork.codec,
  latestBlockHeader : BeaconBlockHeader := BeaconBlockHeader.codec,
  blockRoots : Array ByteArray := vec bytes32 (fun p => p.slotsPerHistoricalRoot),
  stateRoots : Array ByteArray := vec bytes32 (fun p => p.slotsPerHistoricalRoot),
  historicalRoots : Array ByteArray := list bytes32 (fun _ => historicalRootsLimit),
  eth1Data : Eth1Data := Eth1Data.codec,
  eth1DataVotes : Array Eth1Data := list Eth1Data.codec (fun p => p.epochsPerEth1VotingPeriod * p.slotsPerEpoch),
  eth1DepositIndex : Nat := u64,
  validators : Array Validator := list Validator.codec (fun _ => validatorRegistryLimit),
  balances : Array Nat := list u64 (fun _ => validatorRegistryLimit),
  randaoMixes : Array ByteArray := vec bytes32 (fun p => p.epochsPerHistoricalVector),
  slashings : Array Nat := vec u64 (fun p => p.epochsPerSlashingsVector),
  previousEpochParticipation : ByteArray := byteList (fun _ => validatorRegistryLimit),
  currentEpochParticipation : ByteArray := byteList (fun _ => validatorRegistryLimit),
  justificationBits : Array Bool := bitvector (fun _ => justificationBitsLength),
  previousJustifiedCheckpoint : Checkpoint := Checkpoint.codec,
  currentJustifiedCheckpoint : Checkpoint := Checkpoint.codec,
  finalizedCheckpoint : Checkpoint := Checkpoint.codec,
  inactivityScores : Array Nat := list u64 (fun _ => validatorRegistryLimit),
  currentSyncCommittee : SyncCommittee := SyncCommittee.codec,
  nextSyncCommittee : SyncCommittee := SyncCommittee.codec,
  latestExecutionPayloadHeader : ExecutionPayloadHeader := ExecutionPayloadHeader.codec,
  nextWithdrawalIndex : Nat := u64,
  nextWithdrawalValidatorIndex : Nat := u64,
  historicalSummaries : Array HistoricalSummary := list HistoricalSummary.codec (fun _ => historicalRootsLimit),
  depositRequestsStartIndex : Nat := u64,
  depositBalanceToConsume : Nat := u64,
  exitBalanceToConsume : Nat := u64,
  earliestExitEpoch : Nat := u64,
  consolidationBalanceToConsume : Nat := u64,
  earliestConsolidationEpoch : Nat := u64,
  pendingDeposits : Array PendingDeposit := list PendingDeposit.codec (fun _ => pendingDepositsLimit),
  pendingPartialWithdrawals : Array PendingPartialWithdrawal := list PendingPartialWithdrawal.codec (fun p => p.pendingPartialWithdrawalsLimit),
  pendingConsolidations : Array PendingConsolidation := list PendingConsolidation.codec (fun p => p.pendingConsolidationsLimit),
  proposerLookahead : Array Nat := vec u64 (fun p => (minSeedLookahead + 1) * p.slotsPerEpoch)

/-! The `Deltas` container of the `rewards` vectors. -/
ssz_container Deltas where
  rewards : Array Nat := list u64 (fun _ => validatorRegistryLimit),
  penalties : Array Nat := list u64 (fun _ => validatorRegistryLimit)

/-! Containers outside the state transition, covered by `ssz_static`. -/

ssz_container AggregateAndProof where
  aggregatorIndex : Nat := u64,
  aggregate : Attestation := Attestation.codec,
  selectionProof : ByteArray := bytes96

ssz_container SignedAggregateAndProof where
  message : AggregateAndProof := AggregateAndProof.codec,
  signature : ByteArray := bytes96

ssz_container SyncCommitteeMessage where
  slot : Nat := u64,
  beaconBlockRoot : ByteArray := bytes32,
  validatorIndex : Nat := u64,
  signature : ByteArray := bytes96

ssz_container SyncCommitteeContribution where
  slot : Nat := u64,
  beaconBlockRoot : ByteArray := bytes32,
  subcommitteeIndex : Nat := u64,
  aggregationBits : Array Bool := bitvector (fun p => p.syncCommitteeSize / 4),
  signature : ByteArray := bytes96

ssz_container ContributionAndProof where
  aggregatorIndex : Nat := u64,
  contribution : SyncCommitteeContribution := SyncCommitteeContribution.codec,
  selectionProof : ByteArray := bytes96

ssz_container SignedContributionAndProof where
  message : ContributionAndProof := ContributionAndProof.codec,
  signature : ByteArray := bytes96

ssz_container SyncAggregatorSelectionData where
  slot : Nat := u64,
  subcommitteeIndex : Nat := u64

ssz_container Eth1Block where
  timestamp : Nat := u64,
  depositRoot : ByteArray := bytes32,
  depositCount : Nat := u64

ssz_container PowBlock where
  blockHash : ByteArray := bytes32,
  parentHash : ByteArray := bytes32,
  totalDifficulty : Nat := u256

ssz_container BlobIdentifier where
  blockRoot : ByteArray := bytes32,
  index : Nat := u64

ssz_container BlobSidecar where
  index : Nat := u64,
  blob : ByteArray := bytesN 131072,
  kzgCommitment : ByteArray := bytes48,
  kzgProof : ByteArray := bytes48,
  signedBlockHeader : SignedBeaconBlockHeader := SignedBeaconBlockHeader.codec,
  kzgCommitmentInclusionProof : Array ByteArray := vec bytes32 (fun _ => 17)

ssz_container DataColumnsByRootIdentifier where
  blockRoot : ByteArray := bytes32,
  columns : Array Nat := list u64 (fun _ => 128)

ssz_container DataColumnSidecar where
  index : Nat := u64,
  column : Array ByteArray := list (bytesN 2048) (fun _ => maxBlobCommitmentsPerBlock),
  kzgCommitments : Array ByteArray := list bytes48 (fun _ => maxBlobCommitmentsPerBlock),
  kzgProofs : Array ByteArray := list bytes48 (fun _ => maxBlobCommitmentsPerBlock),
  signedBlockHeader : SignedBeaconBlockHeader := SignedBeaconBlockHeader.codec,
  kzgCommitmentsInclusionProof : Array ByteArray := vec bytes32 (fun _ => 4)

ssz_container MatrixEntry where
  cell : ByteArray := bytesN 2048,
  kzgProof : ByteArray := bytes48,
  columnIndex : Nat := u64,
  rowIndex : Nat := u64

ssz_container LightClientHeader where
  beacon : BeaconBlockHeader := BeaconBlockHeader.codec,
  execution : ExecutionPayloadHeader := ExecutionPayloadHeader.codec,
  executionBranch : Array ByteArray := vec bytes32 (fun _ => 4)

ssz_container LightClientBootstrap where
  header : LightClientHeader := LightClientHeader.codec,
  currentSyncCommittee : SyncCommittee := SyncCommittee.codec,
  currentSyncCommitteeBranch : Array ByteArray := vec bytes32 (fun _ => 6)

ssz_container LightClientUpdate where
  attestedHeader : LightClientHeader := LightClientHeader.codec,
  nextSyncCommittee : SyncCommittee := SyncCommittee.codec,
  nextSyncCommitteeBranch : Array ByteArray := vec bytes32 (fun _ => 6),
  finalizedHeader : LightClientHeader := LightClientHeader.codec,
  finalityBranch : Array ByteArray := vec bytes32 (fun _ => 7),
  syncAggregate : SyncAggregate := SyncAggregate.codec,
  signatureSlot : Nat := u64

ssz_container LightClientFinalityUpdate where
  attestedHeader : LightClientHeader := LightClientHeader.codec,
  finalizedHeader : LightClientHeader := LightClientHeader.codec,
  finalityBranch : Array ByteArray := vec bytes32 (fun _ => 7),
  syncAggregate : SyncAggregate := SyncAggregate.codec,
  signatureSlot : Nat := u64

ssz_container LightClientOptimisticUpdate where
  attestedHeader : LightClientHeader := LightClientHeader.codec,
  syncAggregate : SyncAggregate := SyncAggregate.codec,
  signatureSlot : Nat := u64

end Beacon
