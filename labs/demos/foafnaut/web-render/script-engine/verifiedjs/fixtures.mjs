// The script sources of session.test.mjs, lean-dom.test.mjs and
// fixtures/scripted.html, plus the language features they use, one per case.
// A probe run compares the engine under test with Node on the same source.

// A stand-in for the document binding, in ES5, written with objects, closures
// and console.log only. It lets a run separate "no document binding" from
// "the language feature is missing". It is not a DOM.
export const STUB = `
function __node(id, text) {
  var n = { id: id, textContent: text, attrs: {}, click: null };
  n.addEventListener = function (type, callback) { n.click = callback; };
  n.setAttribute = function (name, value) { n.attrs[name] = value; console.log('set', name, value); };
  n.getAttribute = function (name) { return n.attrs[name]; };
  return n;
}
var __message = __node('message', 'before'), __change = __node('change', 'Change');
var document = {
  getElementById: function (id) { if (id === 'message') return __message; if (id === 'change') return __change; return null; },
  querySelector: function (s) { return document.getElementById(s.slice(1)); }
};
function __click() {
  var event = { type: 'click', cancelable: true, defaultPrevented: false, preventDefault: function () { event.defaultPrevented = true; } };
  __change.click.call(__change, event);
}
`;

// The gate: a fixture passes when its output equals Node's. Every case not
// named here is an expected failure of the issue below. A listed case that
// fails, or an unlisted fixture that passes, makes the probe exit 1: flip the
// list and close the issue. Filled from run 42318218843 and its successors.
export const ISSUE = 'https://github.com/danbri/factoidal/issues/1252';
export const PASSING = { core: [], wasm: [] };

export const FIXTURES = [
  ['session-classic-1', `let count = 1; document.getElementById("message").textContent = "loaded"; console.log(document.getElementById("message").textContent);`],
  ['session-classic-2', `let count = 1; document.querySelector("#change").addEventListener("click", function(event) { document.getElementById("message").textContent = "click " + count++; this.setAttribute("data-clicked", event.type); }); __click(); __click(); console.log(document.getElementById("message").textContent);`],
  ['session-anchor', `document.getElementById('change').addEventListener('click', function(event) {
      console.log(event.cancelable, event.defaultPrevented);
      this.setAttribute('href', '/updated-target');
      return false;
    }); __click();`],
  ['session-prevent-default', `let turn = 0, previous;
      const anchor = document.getElementById('change');
      anchor.addEventListener('click', function(event) {
        'use strict';
        try { event.defaultPrevented = true; } catch {}
        console.log('before', event.defaultPrevented);
        if (++turn === 1) { event.preventDefault(); previous = event; }
        else previous.preventDefault();
      }); __click(); __click();`],
  ['session-throw-discards', `try { document.getElementById("message").textContent="discard";throw Error("stop"); } catch (error) { console.log(error.message); }`],
  ['session-allocation', `const big = new Array(1000).fill("x"); console.log(big.length);`],
  ['lean-dom-own-attributes', `
        const absent=document.getElementById('message'),present=document.getElementById('change');
        function check(){
          for(const name of ['toString','constructor','__proto__'])
            if(absent.getAttribute(name)!==undefined&&absent.getAttribute(name)!==null)console.log('inherited attribute leaked: '+name);
        }
        check();
        absent.setAttribute('data-ok','yes');
        check();
        if(absent.getAttribute('data-ok')!=='yes')throw Error('successful attribute lost');
        console.log('own attributes passed');`],
  ['lean-dom-named-error', `
        const child=document.getElementById('message');let rejected=false;
        try{throw Object.assign(Error('x'),{name:'InvalidCharacterError'});}
        catch(error){
          if(!(error instanceof Error)||error.name!=='InvalidCharacterError')throw Error('DOM error name lost');
          rejected=true;
        }
        console.log(rejected);`],
  ['scripted-html', `let clicks = 0;
document.getElementById('message').textContent = 'QuickJS loaded. Click the link.';
document.getElementById('change').addEventListener('click', function () {
  document.getElementById('message').textContent = 'Clicks: ' + (++clicks);
}); __click(); __click(); console.log(document.getElementById('message').textContent);`],
];

export const FEATURES = [
  ['number-add', `console.log(1 + 2);`],
  ['string-literal', `console.log('hello');`],
  ['string-concat', `console.log('a' + 'b');`],
  ['string-number-concat', `console.log('Clicks: ' + 1);`],
  ['string-compare', `console.log('a' === 'a', 'a' === 'b');`],
  ['string-slice', `console.log('#change'.slice(1));`],
  ['string-length', `console.log('abc'.length);`],
  ['console-two-args', `console.log('a', 'b');`],
  ['var-global-update', `var n = 1; n = n + 1; console.log(n);`],
  ['let-global-update', `let n = 1; n = n + 1; console.log(n);`],
  ['closure-read', `var n = 7; function f() { return n; } console.log(f());`],
  ['closure-write', `var n = 0; function f() { n = n + 1; } f(); f(); console.log(n);`],
  ['closure-counter', `function mk() { var c = 0; return function () { c = c + 1; return c; }; } var g = mk(); g(); console.log(g());`],
  ['function-one-arg', `function f(a) { return a; } console.log(f(5));`],
  ['function-two-args', `function f(a, b) { return a + b; } console.log(f(2, 3));`],
  ['function-as-value', `function f(g) { return g(2); } console.log(f(function (x) { return x + 1; }));`],
  ['object-prop', `var o = { a: 1 }; o.b = 2; console.log(o.a + o.b);`],
  ['object-17-props', `var o = {}; o.a=1;o.b=2;o.c=3;o.d=4;o.e=5;o.f=6;o.g=7;o.h=8;o.i=9;o.j=10;o.k=11;o.l=12;o.m=13;o.n=14;o.o=15;o.p=16;o.q=17; console.log(o.q);`],
  ['object-computed-key', `var o = {}; var k = 'a'; o[k] = 1; console.log(o.a);`],
  ['method-this', `var o = { n: 3, f: function () { return this.n; } }; console.log(o.f());`],
  ['call-with-this', `function f() { return this.n; } console.log(f.call({ n: 4 }));`],
  ['array-index', `var a = [1, 2, 3]; console.log(a[1]);`],
  ['array-length', `var a = [1, 2, 3]; console.log(a.length);`],
  ['for-of', `var t = 0; for (const x of [1, 2]) t = t + x; console.log(t);`],
  ['for-in', `var o = { a: 1 }; for (var k in o) console.log(k);`],
  ['try-catch-local', `try { throw 1; } catch (e) { console.log(e); }`],
  ['try-catch-across-call', `function f() { throw 2; } try { f(); console.log('continued'); } catch (e) { console.log('caught', e); }`],
  ['uncaught-throw-stops', `console.log('a'); throw 1; console.log('b');`],
  ['error-constructor', `var e = Error('stop'); console.log(e.message);`],
  ['instanceof', `function A() {} console.log(new A() instanceof A);`],
  ['typeof-undeclared', `console.log(typeof nothing);`],
  ['increment', `var c = 0; console.log(++c, c++, c);`],
  ['arrow', `var f = x => x + 1; console.log(f(1));`],
  ['json-stringify', `console.log(JSON.stringify({ a: 1 }));`],
  ['map-set', `var m = new Map(); m.set('a', 1); console.log(m.get('a'));`],
  ['spread', `var a = [1]; var b = [...a, 2]; console.log(b.length);`],
  ['object-freeze', `var o = Object.freeze({ a: 1 }); o.a = 2; console.log(o.a);`],
  ['getter', `var o = { get a() { return 1; } }; console.log(o.a);`],
  ['global-this', `console.log(typeof globalThis);`],
  ['infinite-loop', `while (true) {}`],
  ['heap-growth', `var i = 0; var o; while (i < 2000) { o = { a: i }; i = i + 1; } console.log(o.a);`],
];
