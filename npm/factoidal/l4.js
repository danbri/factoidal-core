// @factoidal/core/l4: an alias of the main entry, kept for 0.9.x.
// Until 0.9.0 this path was the low-level Lean loader and `.` was the F*
// engine; the main entry is the Lean engine now (loadEngine() gives the
// low-level handle). This alias goes in 0.10.0 (CHANGELOG.md).

'use strict';

module.exports = require('./index.js');
