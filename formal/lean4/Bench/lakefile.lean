import Lake
open Lake DSL

package l4factoidal

lean_lib L4Factoidal

lean_exe «l4sparql-index-bench» where
  root := `Bench.SparqlIndexBench
