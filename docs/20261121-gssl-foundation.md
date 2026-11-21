# GpuDomainSpecificLanguage (GSSL): foundation

GSSL is the chosen name for the workload-independent GPU programming language.
This first step exposes the existing typed Paralliverse composition layer; it
does not claim the full language or a general GPU compiler is complete.

The existing `Shape`, `Signature`, `Program` and `Program.eval` provide typed,
pure composition, product, fanout and list map. A domain chooses its scalar
types, primitive symbols and meanings. The program syntax contains symbols,
not arbitrary Lean function literals. `Program.runCPU_eq_eval` proves that the
task-based CPU interpretation agrees with the reference interpretation when
all primitive implementations agree. `Program.eval_fuseMaps` proves pure map
fusion preserves that interpretation.

The GSSL module adds `eval_eq_of_primitive_agreement`: for every typed program,
agreement between any two primitive interpretations implies agreement for the
whole program. This property is independent of SPARQL and applies equally to
other domain languages that lower to the same syntax. It follows from the
existing CPU refinement theorem; it is not a new proof of GPU correctness.

## Runtime source and domain-specific theorems

A domain language can parse an input string and lower accepted syntax to a
GSSL program. Parsing and execution do not require `sorry` or `admit`, or a
new proof per input. General theorems apply only when their premises are met.
A separate theorem relating the parser and lowering to the domain's semantics
is needed before claiming that an arbitrary input string has its intended
meaning. Particular properties may be established by a proved checker, a
supplied proof, or runtime Lean proof checking; no runtime Lean integration is
added here. An unfinished proof remains unfinished even when invoked at runtime.

## Open boundaries

The current typed composition language is not yet the proposed bounded kernel
language with explicit GPU buffers, work items and barriers. Its signatures can
include arbitrary pure primitive meanings; neither the generic theorem nor the
type system establishes buffer safety, race freedom, bounded resource use or
actual GPU support for arbitrary primitives. The existing Studio's fixed BGP
WGSL kernels are not automatically generated from arbitrary `Program` syntax.

Future work: define a bounded kernel subset and GPU memory semantics; prove
generic map, filter, scan, scatter and reduction properties with explicit
preconditions; define and verify a WGSL lowering; build separate domain DSLs
and their correctness theorems; then connect optional browser Lean checking.
Actual drivers, physical GPU behaviour and the browser/host remain explicit
trust and testing boundaries.
