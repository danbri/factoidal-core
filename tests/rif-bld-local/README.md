# Project-local RIF BLD cases

Corrected copies of W3C RIF BLD cases whose test data is defective
(https://github.com/danbri/factoidal/issues/1186 (built-in written without
`External`)). Each directory holds the W3C premise unchanged and the
conclusion with `pred:iri-string(...)` written as
`External(pred:iri-string(...))`, which is what the test description says.
`lake exe l4rif --bld` runs them as the `rif-bld-local` line; every case must
pass.
