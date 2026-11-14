export const sq = x => x * x;
export function sum(xs) { let s = 0; for (const x of xs) s += x; return s; }
export class Counter { constructor() { this.n = 0; } inc() { return ++this.n; } }
