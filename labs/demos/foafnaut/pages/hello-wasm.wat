;; A module for the page foafnaut:wasm (issue 1244): run by WasmVM, the WebAssembly
;; engine written in Lean, inside the Foafnaut engine. Address bar: :wasm hello-wasm.wasm#main
;; Made with: wasm-tools parse hello-wasm.wat -o hello-wasm.wasm
(module
  (import "spectest" "print_i32" (func $print (param i32)))
  (memory 1)
  (func $fib (param $n i32) (result i32)
    (if (result i32) (i32.lt_u (local.get $n) (i32.const 2))
      (then (local.get $n))
      (else (i32.add (call $fib (i32.sub (local.get $n) (i32.const 1)))
                     (call $fib (i32.sub (local.get $n) (i32.const 2)))))))
  ;; Prints 1, 2 and 3, writes fib(0..19) into memory and returns the sum of what it reads back.
  (func (export "main") (result i32) (local $i i32) (local $acc i32)
    (call $print (i32.const 1)) (call $print (i32.const 2)) (call $print (i32.const 3))
    (block $done (loop $l
      (br_if $done (i32.ge_u (local.get $i) (i32.const 20)))
      (i32.store (i32.shl (local.get $i) (i32.const 2)) (call $fib (local.get $i)))
      (local.set $acc (i32.add (local.get $acc) (i32.load (i32.shl (local.get $i) (i32.const 2)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $acc))
  (func (export "fib") (param i32) (result i32) (call $fib (local.get 0))))
