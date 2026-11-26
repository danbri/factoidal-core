# Setting up Lean 4

## 1. Check the installation

Run `scripts/check_lean.sh`. It prints whether `elan` / `lean` / `lake` are present and their versions.

## 2. Install (if missing; get the user's confirmation first)

`elan` is Lean's toolchain manager (the equivalent of rustup for Rust).

```bash
# macOS (Homebrew)
brew install elan-init
# or the official installer
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

After installing, restart the shell and run `elan default stable` to make the latest stable release the default.
**The first run takes minutes to download the toolchain.** Calling `lean` concurrently makes elan wait on a lock, so wait for it to finish.

## 3. Try it in a single file (core only)

`bv_decide` / `omega` / `decide` / `simp` / `#eval` all work with core alone.

```bash
lean file.lean        # no error = proof succeeded; counterexamples appear as errors
```

Put `import Std.Tactic.BVDecide` at the top of the file to use `bv_decide`.

## 4. Add plausible (when you need property-based testing; get the user's permission first)

Plausible is a `lake` dependency, not part of core. Skip this section if `bv_decide` / `#eval` can answer the question (fixed-width integers, small finite domains).

1. **Check**: run `scripts/check_lean.sh` from the project. `plausible: available` means you are done. `plausible: not installed` means continue. `plausible: unavailable (single-file mode)` means there is no lake project yet.
2. **Choose the target**: add it to the existing lake project if there is one. Otherwise create a working project in the scratchpad (`lake new myproof`, then `cd myproof`) instead of touching the user's repository.
3. **Ask for permission**, and say in the request:
   - which files change (`lakefile.toml` of the target project, plus a new `lake-manifest.json` and `.lake/`),
   - that `lake update` fetches the dependency from GitHub over the network,
   - that the first `lake build` takes extra time.
4. **Only after the user agrees**, append the dependency and build. Never edit `lakefile.toml` or run `lake update` before that.

```bash
cat >> lakefile.toml <<'EOF'

[[require]]
name = "plausible"
scope = "leanprover-community"
rev = "v4.36.0"       # match the version reported by `lean --version`
EOF
lake update && lake build Plausible   # plain `lake build` skips dependencies that nothing imports
```

- Match `rev` to the version tag of the toolchain you use (a mismatch makes dependency resolution fail).
- `plausible` makes the **build fail** when it finds a counterexample. If `Found a counter-example!` appears with a shrunk input, that is a success signal (a bug was found).
- When you need Mathlib (`ring_nf`, `linarith`, ...) use `lake new myproof math`, but the first build is very heavy, so avoid it until it is really needed.

## 5. Where to work

Put trial-and-error files outside the repository (e.g. a scratchpad). If you keep verification results in the repository, put them in a dedicated directory such as `proofs/` and add the build output `.lake/` to `.gitignore`.
