// The Data and documents page's entry: a module file, since the page's policy allows no inline script.
import {mount} from './specs.mjs';

mount(document.getElementById('app'), {base: new URL('./', import.meta.url).href});
