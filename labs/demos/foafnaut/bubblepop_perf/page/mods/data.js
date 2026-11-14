import { sq } from "./util.js";
export const table = Array.from({ length: 200 }, (_, i) => sq(i % 17));
export default function lookup(i) { return table[i % table.length]; }
