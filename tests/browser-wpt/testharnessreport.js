// Foafnaut's testharnessreport.js (this repository's own file; a WPT runner supplies its
// own testharnessreport.js, as wptrunner does). The runner (testharness-run.ts) serves it
// in place of /resources/testharnessreport.js. Results leave the page as console lines,
// which the Lean script session keeps: one per subtest, then one for the harness.
setup({ output: false });
add_result_callback(function (t) {
  console.log('__wpt_result ' + JSON.stringify({ name: String(t.name), status: t.status,
    message: t.message === null || t.message === undefined ? null : String(t.message).slice(0, 300) }));
});
add_completion_callback(function (tests, status) {
  console.log('__wpt_done ' + JSON.stringify({ status: status.status,
    message: status.message === null || status.message === undefined ? null : String(status.message).slice(0, 300),
    tests: tests.length }));
});
