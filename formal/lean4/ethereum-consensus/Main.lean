import EthereumConsensus

/-! Machine-readable synthetic SSZ position observations for independent
    checking against consensus-spec generalized-index formulas. -/

def main : IO Unit := do
  for i in [:1025] do
    IO.println s!"{i}\t{EthereumConsensus.SSZ.parent i}\t{EthereumConsensus.SSZ.sibling i}\t{EthereumConsensus.SSZ.depth i}"
