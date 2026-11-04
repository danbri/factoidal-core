# Fresh registry inventory for the web rendering tree

The fresh generator ran against web source
`ff6d8c3853341562c24ea7f17d4dd4ef8cea6964`, with only the dataflow workflow
artifact patch added in `94b8a6caa644fab2afc197e50fdbbcbd3ca4822f`.
The formal Lean and lab trees are identical between those two commits.

Run: https://github.com/danbri/factoidal-core/actions/runs/41550488941.
The fresh Registry/RegistryTests build, generation, complete dataflow gate
(including the negative registry tests and both inventory `--check` results),
and npm job passed. Only the final committed-output drift check failed.

Actual generator output adds both `Rendering` and `UI` to unnamed component
directories, changing 47/73 to 49/75. These are directory inventory counts,
not renderer passes or declared dataflow stages. `StageKinds.lean` remains
byte-identical. Both files were copied from the generated artifact after
checking its source witness and hashes; no generated content was edited.

Artifact:
https://github.com/danbri/factoidal-core/actions/runs/41550488941/artifacts/13193655733.
Zip SHA-256:
`7242d386210939805fc2aeac9dea7738520ad6a87248fed5fed1096823c7f4ed`.
Generated inventory SHA-256:
`3773b197cb2ddd7d5b37edebf063ee0f35d16ee947cc4125046e15fd43773d05`.
Unchanged stage kinds:
`ddbed64fd748a7d46174da0ac05d373af1803b593f497066d6ded2be04f99bf7`.
Generator:
`daec833259ef95d97ed60f251d83dd85d5a8b13f62202b0a67633daf2b5b5634`.
Lean 4.33.1, compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.

The local CI wrapper checkout is sparse to save disk; the GitHub job uses a
full checkout and performs the actual source-directory walk. No released WASM
or cached report replaced fresh Lean registry generation. A subsequent run
must confirm the committed generated files remain current.
