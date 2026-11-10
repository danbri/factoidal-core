// Host names that single-file library builds look for. No language feature is added here.
var module = { exports: {} };
var exports = module.exports;
if (typeof console === 'undefined') { globalThis.console = { log: print }; }
function lcg(seed) { var s = seed >>> 0; return function () { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s; }; }
function mix(h, x) { return (Math.imul(h ^ (x | 0), 16777619) + 0x9e3779b9) | 0; }
function mixStr(h, s) { for (var i = 0; i < s.length; i++) h = mix(h, s.charCodeAt(i)); return h; }
