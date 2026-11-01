# Preserve QName namespaces in fn:transform serialization parameters

Date: 2026-10-29. Tracking:
https://github.com/danbri/factoidal/issues/1161 and
https://github.com/danbri/factoidal/issues/1101.

`QtFnTransform.propString` already converted a singleton QName to its EQName,
but a sequence of QNames went through `Atomic.str` and lost the namespace URI.
Consequently, `cdata-section-elements` and `suppress-indentation` could apply
to the wrong element when the caller supplied more than one QName.

The sequence conversion now uses `QN.eqn` for each QName and retains
`Atomic.str` for other atomic values. Four public `fn:transform` guards check
multi-name parameters, singleton controls, equal local names in different
namespaces, and merging with the stylesheet's output declaration. The new
`QtFnTransformTests` module is imported by the library root.

Validation on macOS ARM64, with the existing QT4 fixtures:

- Before the fix, the two multi-QName guards failed; both singleton controls
  passed. After the fix, all four passed.
- `lake build L4Factoidal.XSLT4.QtFnTransformTests l4qt4` passed, run with
  `formal/lean4` as the working directory.
- `.lake/build/bin/l4qt4 --lang xquery --set fn-transform --list-fails --isolate 60`
  changed from 127 pass, 9 fail, 1 unsupported to 129 pass, 7 fail,
  1 unsupported, out of 137. Cases `fn-transform-65` and `fn-transform-66`
  now pass. No fixtures, exclusions, or feature settings changed.
- Remaining failures: 27, 67, 70, 82e, 91, 94, err-9a. Case 48 still needs
  selectable older-language behavior and remains outstanding.

The same diagnosis pass measured `fn-load-xquery-module` at 181 pass, 1 fail,
2 unsupported, out of 184. Case 050 needs named schema atomic types below
the loader: preserving the restriction and type annotation, not replacing
the type with its built-in base. Cases 023 and 070 need older-language modes.
Those findings do not change code in this patch.

These are targeted checks, not a full-library or WASM build. This patch is
stacked on https://github.com/danbri/factoidal-core/pull/266.
