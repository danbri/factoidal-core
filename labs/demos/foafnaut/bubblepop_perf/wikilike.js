// A script workload in the style of a large wiki's start-up code (an original construct, no
// copied code): a module registry whose modules are closures, a jQuery-like chained wrapper
// over plain objects, message formatting with replacements, a hook (event) registry, and
// a table of page data built and searched. Library code of this kind is made of closures,
// so it measures the share of calls the register machine takes.
// `N` scales the work; it prints one line `RESULT <checksum>`.
var N = typeof N === 'number' ? N : 200;

(function (global) {
  'use strict';
  var registry = {};
  var loaded = {};
  function define(name, deps, factory) {
    registry[name] = { deps: deps, factory: factory, exports: null };
  }
  function require(name) {
    if (loaded[name]) return registry[name].exports;
    var m = registry[name];
    var args = m.deps.map(function (d) { return require(d); });
    m.exports = m.factory.apply(null, args);
    loaded[name] = true;
    return m.exports;
  }

  define('util', [], function () {
    function each(list, fn) {
      for (var i = 0; i < list.length; i++) {
        if (fn.call(list[i], i, list[i]) === false) break;
      }
      return list;
    }
    function extend(target) {
      for (var i = 1; i < arguments.length; i++) {
        var src = arguments[i];
        for (var k in src) {
          if (Object.prototype.hasOwnProperty.call(src, k)) target[k] = src[k];
        }
      }
      return target;
    }
    function escapeHtml(s) {
      return String(s).replace(/[&<>"]/g, function (c) {
        return c === '&' ? '&amp;' : c === '<' ? '&lt;' : c === '>' ? '&gt;' : '&quot;';
      });
    }
    return { each: each, extend: extend, escapeHtml: escapeHtml };
  });

  define('hooks', ['util'], function (util) {
    var lists = {};
    function hook(name) {
      var list = lists[name] || (lists[name] = []);
      return {
        add: function (fn) { list.push(fn); return this; },
        fire: function () {
          var args = Array.prototype.slice.call(arguments);
          var n = 0;
          util.each(list, function (i, fn) { n += fn.apply(null, args) || 0; });
          return n;
        }
      };
    }
    return hook;
  });

  define('message', ['util'], function (util) {
    var store = {};
    function set(key, text) { store[key] = text; }
    function format(key) {
      var params = Array.prototype.slice.call(arguments, 1);
      var text = store[key] || ('<' + key + '>');
      return text.replace(/\$(\d+)/g, function (m, d) {
        var v = params[d - 1];
        return v === undefined ? m : util.escapeHtml(v);
      });
    }
    return { set: set, format: format };
  });

  define('query', ['util'], function (util) {
    function Q(items) {
      if (!(this instanceof Q)) return new Q(items);
      this.items = items || [];
      this.length = this.items.length;
    }
    Q.prototype.filter = function (pred) {
      var out = [];
      util.each(this.items, function (i, x) { if (pred(x, i)) out.push(x); });
      return new Q(out);
    };
    Q.prototype.map = function (fn) {
      var out = [];
      for (let i = 0; i < this.items.length; i++) out.push(fn(this.items[i], i));
      return new Q(out);
    };
    Q.prototype.attr = function (k, v) {
      if (v === undefined) return this.items.length ? this.items[0][k] : undefined;
      util.each(this.items, function () { this[k] = v; });
      return this;
    };
    Q.prototype.addClass = function (c) {
      return this.attr('class', (this.attr('class') ? this.attr('class') + ' ' : '') + c);
    };
    Q.prototype.text = function () {
      var s = '';
      this.items.forEach(function (x) { s += x.text || ''; });
      return s;
    };
    return Q;
  });

  define('page', ['util', 'hooks', 'message', 'query'], function (util, hook, msg, Q) {
    msg.set('edit-count', 'Edited $1 times by $2');
    msg.set('section', '<h2 id="$1">$2</h2>');
    var sectionsHook = hook('sections');
    sectionsHook.add(function (secs) { return secs.length; })
      .add(function (secs) { return secs.filter(function (s) { return s.level === 2; }).length; });
    function buildPage(seed) {
      var sections = [];
      for (var i = 0; i < 40; i++) {
        var id = 'sec-' + seed + '-' + i;
        sections.push({ id: id, level: 2 + (i % 3), text: 'Section ' + i + ' of page ' + seed });
      }
      var counts = {};
      var html = '';
      Q(sections)
        .filter(function (s) { return s.level < 4; })
        .map(function (s, i) { return util.extend({}, s, { n: i }); })
        .items.forEach(function (s) {
          html += msg.format('section', s.id, s.text);
          counts[s.level] = (counts[s.level] || 0) + 1;
        });
      var fired = sectionsHook.fire(sections);
      var title = Q([{ text: 'Page ' + seed }]).addClass('mw-title').addClass('x').attr('class');
      return html.length + fired + title.length + Object.keys(counts).length +
        msg.format('edit-count', seed, '<user>').length;
    }
    return { buildPage: buildPage };
  });

  var page = require('page');
  var sum = 0;
  for (var p = 0; p < N; p++) sum = (sum + page.buildPage(p)) % 1000000007;
  global.print ? global.print('RESULT ' + sum) : console.log('RESULT ' + sum);
})(this);
