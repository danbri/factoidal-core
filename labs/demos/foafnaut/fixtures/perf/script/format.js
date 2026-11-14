export const plural = (n, w) => n + " " + w + (n === 1 ? "" : "s");
export const pad = (s, n) => (s + " ".repeat(n)).slice(0, n);
