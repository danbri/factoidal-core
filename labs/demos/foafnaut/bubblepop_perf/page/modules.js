// A module graph (main imports view, view imports data and util, data imports util), loaded
// through the host and then used: the loader and linking, then calls across module bindings.
import { render } from "./mods/view.js";
import { sum } from "./mods/util.js";
globalThis.RESULT = render(SCALE * 3000) + sum([1, 2, 3]);
