# QT4 literal resource bases

Regression coverage for the resource preload in `Harness/Qt4Run.lean`.
Tracking: https://github.com/danbri/factoidal/issues/1101
([work announcement](https://github.com/danbri/factoidal/issues/1101#issuecomment-6509510463)).

Run `tests/qt4-resource-base/run.sh` from the repository root after building
the named `l4qt4` target with `formal/lean4` as the working directory.
The script does not build. `L4QT4` may select an existing runner executable.
It requires exactly 12 pass, 0 fail, 0 unsupported (out of 12).

The local catalog exercises:

- An inline stylesheet whose base names an existing file.
- A nonexistent base filename in an existing directory.
- Two directories with different resources named `shared.xsl`, selected
  by separate stylesheet bases in the same query.
- An external query with a relative stylesheet location.
- Direct and inferred parent traversal outside the suite root. Sentinel
  resources exist outside `suite/`, so these checks reject real readable
  files rather than relying on absent data.
- Same-named parameter and earlier-query resources cannot supply an absent
  external-query target; an existing query-relative target still wins.
- Explicit virtual static bases work for direct and inferred resources;
  an undefined static base does not enable preload.

The scanner extracts literal path tokens without interpreting options or
parsing embedded stylesheets. Parent directories of literal paths supply
candidate directories; other literal tokens are tried relative to them.
The query-input registry scopes every candidate to its input's absolute URI
base, without raw aliases across input bases. Explicit static bases supply
the logical URI; fixture directories supply the bytes. Inferred file URI
keys are rebased into the same logical URI space. Source-stylesheet and
module scanning retain their existing behavior. `normPath`
rejects paths above the suite root; alternate candidates also undergo a
canonical root check before loading. No directory contents are enumerated
for preload discovery.

This supplies literal resources only. Computed resource locations still
require a resource provider; the scanner does not evaluate expressions to
find resources.

On 2026-10-29 the fixture set changed from 3 pass, 3 fail, 0 unsupported to
6 pass, 0 fail, 0 unsupported (out of 6). The official XQuery `fn-transform`
set changed from 131 pass, 5 fail, 1 unsupported to 132 pass, 4 fail,
1 unsupported (out of 137), fixing `fn-transform-err-9a` and retaining the
parent's `fn-transform-94` correction.

The six additional input-identity controls initially produced 9 pass,
3 fail, 0 unsupported (out of 12): both absent-target cases returned the
wrong file, and the virtual-base inferred include was unavailable. After
scoping the input registry they give 12 pass, 0 fail, 0 unsupported.
The official `fn-transform` result remains 132 pass, 4 fail, 1 unsupported.
