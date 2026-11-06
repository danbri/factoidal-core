# Compositor folder navigation and save destination

`PipelineLibrary.browse()` previously changed its current folder before the
LWS listing completed. If listing failed, the displayed folder and entries
stayed unchanged, but **Save as new file** used the failed folder as its
destination. A pod can permit writing where listing is denied, so the failure
could cause a successful save somewhere other than the displayed location.

The component now keeps the candidate folder local until the listing succeeds
and its option elements are prepared. It then updates the entries, current
folder and displayed location in the same synchronous turn. No LWS access
policy, credential handling or overwrite precondition changes.

Validation:

```sh
node --test tests/hub/compositor_browse_atomicity_test.mjs
```

Three tests import the actual component with minimal browser-interface stubs.
They check rejected navigation, pending/successful navigation and an invalid
listing. The rejection case also checks the subsequent save URL. This is a
component state regression test, not a browser/CORS interoperability test.
