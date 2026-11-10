// Node/Chrome: print as the engine shells have it; run the file given (Node only).
globalThis.print = (...a) => console.log(a.join(" "));
require("vm").runInThisContext(require("fs").readFileSync(process.argv[2], "utf8"), process.argv[2]);
