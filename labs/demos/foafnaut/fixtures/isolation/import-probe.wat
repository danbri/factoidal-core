;; A stand-in for a compromised page script engine (origin isolation check C1, issue 518).
;; The model's attacker is the page's realm with any import call and any argument: this guest
;; module has the exports Hosts.Page asks of a script engine and, on every script, callback
;; and event, walks the node numbers of the arena through `foafnaut_dom` and logs
;; "doc <d> text <t>" for each text node, and "wrote <d> <code>" after trying to change it.
;; The test (origin_isolation_test.ts) fails if a text of a cross-origin frame's document is
;; logged or written. Original fixture; no page content.
(module
  (import "foafnaut_dom" "node_info" (func $info (param i32 i32) (result i32)))
  (import "foafnaut_dom" "text_content_get" (func $text (param i32 i32 i32) (result i32)))
  (import "foafnaut_dom" "text_content_set" (func $settext (param i32 i32 i32) (result i32)))
  (import "foafnaut_dom" "console_log" (func $log (param i32 i32) (result i32)))
  (import "foafnaut_dom" "set_timer" (func $timer (param i32 i32 i32) (result i32)))
  (memory (export "memory") 2)
  ;; 8..15 the result block (status 0, no text); 256.. "X";
  ;; 1024.. a line; the heap from 65536
  (data (i32.const 256) "X")
  (global $heap (mut i32) (i32.const 65536))
  (global $armed (mut i32) (i32.const 0))
  ;; write the decimal of $v at $p; answer the end
  (func $dec (param $p i32) (param $v i32) (result i32)
    (local $q i32) (local $t i32) (local $n i32)
    (if (i32.lt_s (local.get $v) (i32.const 0))
      (then (i32.store8 (local.get $p) (i32.const 45))
            (local.set $p (i32.add (local.get $p) (i32.const 1)))
            (local.set $v (i32.sub (i32.const 0) (local.get $v)))))
    (local.set $t (local.get $v)) (local.set $n (i32.const 1))
    (block $b (loop $l
      (br_if $b (i32.lt_u (local.get $t) (i32.const 10)))
      (local.set $t (i32.div_u (local.get $t) (i32.const 10)))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (br $l)))
    (local.set $q (i32.add (local.get $p) (local.get $n)))
    (loop $m
      (local.set $q (i32.sub (local.get $q) (i32.const 1)))
      (i32.store8 (local.get $q) (i32.add (i32.const 48) (i32.rem_u (local.get $v) (i32.const 10))))
      (local.set $v (i32.div_u (local.get $v) (i32.const 10)))
      (br_if $m (i32.gt_u (local.get $q) (local.get $p))))
    (i32.add (local.get $p) (local.get $n)))
  (func $probe
    (local $n i32) (local $doc i32) (local $p i32) (local $len i32) (local $r i32)
    (local.set $n (i32.const 0))
    (block $done (loop $each
      ;; every number up to 512, past refusals (-2): the fixtures have fewer nodes
      (br_if $done (i32.gt_u (local.get $n) (i32.const 512)))
      (local.set $r (call $info (local.get $n) (i32.const 0)))
      (if (i32.eq (local.get $r) (i32.const 3))
        (then
          (local.set $doc (call $info (local.get $n) (i32.const 7)))
          ;; "doc <d> text <t>"
          (i32.store (i32.const 1024) (i32.const 0x20636f64)) ;; "doc "
          (local.set $p (call $dec (i32.const 1028) (local.get $doc)))
          (i32.store (local.get $p) (i32.const 0x78657420)) ;; " tex"
          (i32.store16 (i32.add (local.get $p) (i32.const 4)) (i32.const 0x2074)) ;; "t "
          (local.set $p (i32.add (local.get $p) (i32.const 6)))
          (local.set $len (call $text (local.get $n) (local.get $p) (i32.const 2048)))
          (if (i32.ge_s (local.get $len) (i32.const 0))
            (then (if (i32.le_s (local.get $len) (i32.const 2048))
              (then (drop (call $log (i32.const 1024)
                (i32.add (i32.sub (local.get $p) (i32.const 1024)) (local.get $len))))))))
          ;; a change from this realm to a text node of another document
          (if (i32.ne (local.get $doc) (i32.const 0))
            (then
              (local.set $r (call $settext (local.get $n) (i32.const 256) (i32.const 1)))
              (i32.store (i32.const 1024) (i32.const 0x746f7277)) ;; "wrot"
              (i32.store16 (i32.const 1028) (i32.const 0x2065)) ;; "e "
              (local.set $p (call $dec (i32.const 1030) (local.get $doc)))
              (i32.store8 (local.get $p) (i32.const 32))
              (local.set $p (call $dec (i32.add (local.get $p) (i32.const 1)) (local.get $r)))
              (drop (call $log (i32.const 1024) (i32.sub (local.get $p) (i32.const 1024))))))))
      (local.set $n (i32.add (local.get $n) (i32.const 1)))
      (br $each))))
  (func (export "_initialize"))
  (func (export "qjs_new") (result i32) (i32.const 0))
  (func (export "qjs_page_mode") (param i32))
  (func (export "qjs_page") (param i32 i32 i32))
  (func (export "qjs_release") (param i32))
  (func (export "qjs_run_job") (result i32) (i32.const 0))
  (func (export "qjs_alloc") (param $n i32) (result i32)
    (local $p i32)
    (local.set $p (global.get $heap))
    (global.set $heap (i32.and (i32.add (i32.add (local.get $p) (local.get $n)) (i32.const 15)) (i32.const -16)))
    (if (i32.gt_u (global.get $heap) (i32.const 131000)) (then (global.set $heap (i32.const 65536)) (local.set $p (i32.const 65536))))
    (local.get $p))
  (func (export "qjs_free") (param i32))
  (func (export "qjs_eval") (param i32 i32) (result i32)
    (if (i32.eqz (global.get $armed))
      (then (global.set $armed (i32.const 1))
            (drop (call $timer (i32.const 1) (i32.const 50) (i32.const 1)))))
    (call $probe) (i32.const 8))
  (func (export "qjs_call") (param i32 i32 i32) (result i32) (call $probe) (i32.const 8))
  (func (export "qjs_dispatch") (param i32 i32 i32 i32) (result i32) (call $probe) (i32.const 8)))
