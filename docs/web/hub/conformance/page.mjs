// The Conformance page's entry: a module file, since the page's policy allows no inline script.
// d3 is the vendored copy (third_party/observable, served at /vendor/observable/).
import {mount} from './conformance.mjs';

mount(document.getElementById('app'), {
  d3url: new URL('../../../vendor/observable/d3.esm.js', import.meta.url).href,
  base: new URL('./', import.meta.url).href,
});
