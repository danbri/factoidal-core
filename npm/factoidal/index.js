// @factoidal/core for require(). The ES module index.mjs is the source;
// Node 22.12 and later load it through require(), so CommonJS and ES module
// callers share one module instance (one engine, one `Dataset` class).

'use strict';

module.exports = require('./index.mjs');
