import { text, query } from "./count.js";
export function status(n, round) { text(query(document, "#count"), String(n)); text(query(document, "#status"), "round " + round); }
