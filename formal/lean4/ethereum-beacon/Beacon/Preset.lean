/-!
# Beacon chain presets and configuration (Fulu)

Constants of the `minimal` and `mainnet` presets and configurations, written
out from the normative tables of ethereum/consensus-specs v1.6.1
(commit 5fa6edcca8ab4cf548653e6680b17b9d3e04d225): `presets/*/{phase0,altair,
bellatrix,capella,deneb,electra,fulu}.yaml` and `configs/{minimal,mainnet}.yaml`.
Only values used by the state transition and the SSZ layouts are carried.
-/

namespace Beacon

structure Preset where
  name : String
  -- phase0
  maxCommitteesPerSlot : Nat
  targetCommitteeSize : Nat
  maxValidatorsPerCommittee : Nat := 2048
  shuffleRoundCount : Nat
  slotsPerEpoch : Nat
  epochsPerEth1VotingPeriod : Nat
  slotsPerHistoricalRoot : Nat
  epochsPerHistoricalVector : Nat
  epochsPerSlashingsVector : Nat
  -- altair
  syncCommitteeSize : Nat
  epochsPerSyncCommitteePeriod : Nat
  -- capella
  maxWithdrawalsPerPayload : Nat
  maxValidatorsPerWithdrawalsSweep : Nat
  -- electra
  pendingPartialWithdrawalsLimit : Nat
  pendingConsolidationsLimit : Nat
  maxPendingPartialsPerWithdrawalsSweep : Nat
  -- configuration
  genesisForkVersion : ByteArray
  capellaForkVersion : ByteArray
  secondsPerSlot : Nat
  minValidatorWithdrawabilityDelay : Nat := 256
  shardCommitteePeriod : Nat
  ejectionBalance : Nat := 16000000000
  churnLimitQuotient : Nat
  minPerEpochChurnLimitElectra : Nat
  maxPerEpochActivationExitChurnLimit : Nat
  /-- Blob schedule entries `(epoch, max blobs per block)`. -/
  blobSchedule : List (Nat × Nat)

def minimal : Preset where
  name := "minimal"
  maxCommitteesPerSlot := 4
  targetCommitteeSize := 4
  shuffleRoundCount := 10
  slotsPerEpoch := 8
  epochsPerEth1VotingPeriod := 4
  slotsPerHistoricalRoot := 64
  epochsPerHistoricalVector := 64
  epochsPerSlashingsVector := 64
  syncCommitteeSize := 32
  epochsPerSyncCommitteePeriod := 8
  maxWithdrawalsPerPayload := 4
  maxValidatorsPerWithdrawalsSweep := 16
  pendingPartialWithdrawalsLimit := 64
  pendingConsolidationsLimit := 64
  maxPendingPartialsPerWithdrawalsSweep := 2
  genesisForkVersion := ⟨#[0, 0, 0, 1]⟩
  capellaForkVersion := ⟨#[3, 0, 0, 1]⟩
  secondsPerSlot := 6
  shardCommitteePeriod := 64
  churnLimitQuotient := 32
  minPerEpochChurnLimitElectra := 64000000000
  maxPerEpochActivationExitChurnLimit := 128000000000
  blobSchedule := []

def mainnet : Preset where
  name := "mainnet"
  maxCommitteesPerSlot := 64
  targetCommitteeSize := 128
  shuffleRoundCount := 90
  slotsPerEpoch := 32
  epochsPerEth1VotingPeriod := 64
  slotsPerHistoricalRoot := 8192
  epochsPerHistoricalVector := 65536
  epochsPerSlashingsVector := 8192
  syncCommitteeSize := 512
  epochsPerSyncCommitteePeriod := 256
  maxWithdrawalsPerPayload := 16
  maxValidatorsPerWithdrawalsSweep := 16384
  pendingPartialWithdrawalsLimit := 134217728
  pendingConsolidationsLimit := 262144
  maxPendingPartialsPerWithdrawalsSweep := 8
  genesisForkVersion := ⟨#[0, 0, 0, 0]⟩
  capellaForkVersion := ⟨#[3, 0, 0, 0]⟩
  secondsPerSlot := 12
  shardCommitteePeriod := 256
  churnLimitQuotient := 65536
  minPerEpochChurnLimitElectra := 128000000000
  maxPerEpochActivationExitChurnLimit := 256000000000
  blobSchedule := [(412672, 15), (419072, 21)]

/-! Constants shared by both presets. -/

def farFutureEpoch : Nat := 18446744073709551615
def unsetDepositRequestsStartIndex : Nat := 18446744073709551615
def genesisSlot : Nat := 0
def genesisEpoch : Nat := 0
def baseRewardsPerEpoch : Nat := 4
def depositContractTreeDepth : Nat := 32
def justificationBitsLength : Nat := 4
def minSeedLookahead : Nat := 1
def maxSeedLookahead : Nat := 4
def minEpochsToInactivityPenalty : Nat := 4
def historicalRootsLimit : Nat := 16777216
def validatorRegistryLimit : Nat := 1099511627776
def baseRewardFactor : Nat := 64
def effectiveBalanceIncrement : Nat := 1000000000
def hysteresisQuotient : Nat := 4
def hysteresisDownwardMultiplier : Nat := 1
def hysteresisUpwardMultiplier : Nat := 5
def minAttestationInclusionDelay : Nat := 1
def maxProposerSlashings : Nat := 16
def maxDeposits : Nat := 16
def maxVoluntaryExits : Nat := 16
def inactivityPenaltyQuotientBellatrix : Nat := 16777216
def proportionalSlashingMultiplierBellatrix : Nat := 3
def inactivityScoreBias : Nat := 4
def inactivityScoreRecoveryRate : Nat := 16
def timelySourceFlagIndex : Nat := 0
def timelyTargetFlagIndex : Nat := 1
def timelyHeadFlagIndex : Nat := 2
def timelySourceWeight : Nat := 14
def timelyTargetWeight : Nat := 26
def timelyHeadWeight : Nat := 14
def syncRewardWeight : Nat := 2
def proposerWeight : Nat := 8
def weightDenominator : Nat := 64
def maxBlsToExecutionChanges : Nat := 16
def maxBlobCommitmentsPerBlock : Nat := 4096
def maxExtraDataBytes : Nat := 32
def maxBytesPerTransaction : Nat := 1073741824
def maxTransactionsPerPayload : Nat := 1048576
def bytesPerLogsBloom : Nat := 256
def minActivationBalance : Nat := 32000000000
def maxEffectiveBalanceElectra : Nat := 2048000000000
def minSlashingPenaltyQuotientElectra : Nat := 4096
def whistleblowerRewardQuotientElectra : Nat := 4096
def pendingDepositsLimit : Nat := 134217728
def maxAttesterSlashingsElectra : Nat := 1
def maxAttestationsElectra : Nat := 8
def maxDepositRequestsPerPayload : Nat := 8192
def maxWithdrawalRequestsPerPayload : Nat := 16
def maxConsolidationRequestsPerPayload : Nat := 2
def maxPendingDepositsPerEpoch : Nat := 16
def maxBlobsPerBlockElectra : Nat := 9
def fullExitRequestAmount : Nat := 0

/-- Domain types, as four-byte prefixes. -/
def domainBeaconProposer : ByteArray := ⟨#[0, 0, 0, 0]⟩
def domainBeaconAttester : ByteArray := ⟨#[1, 0, 0, 0]⟩
def domainRandao : ByteArray := ⟨#[2, 0, 0, 0]⟩
def domainDeposit : ByteArray := ⟨#[3, 0, 0, 0]⟩
def domainVoluntaryExit : ByteArray := ⟨#[4, 0, 0, 0]⟩
def domainSyncCommittee : ByteArray := ⟨#[7, 0, 0, 0]⟩
def domainBlsToExecutionChange : ByteArray := ⟨#[10, 0, 0, 0]⟩

end Beacon
