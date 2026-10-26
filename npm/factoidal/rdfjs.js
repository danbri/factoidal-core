// factoidal/rdfjs for require(): the RDF/JS data model of rdfjs.mjs.
//
// The ES module is the source; this file hands the same module instance
// to CommonJS callers (Node 22.12 and later load an ES module through
// require()), so `instanceof Dataset` holds across both import styles.

'use strict';

module.exports = require('./rdfjs.mjs');
