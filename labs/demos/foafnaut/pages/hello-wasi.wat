;; A WASI Preview 1 module for the page foafnaut:wasm (issue 1244): run by WasmVM, the
;; WebAssembly engine written in Lean, with its deny-by-default WASI host (fd_write to
;; stdout is the only grant it uses). Address bar: :wasm hello-wasi.wasm#_start
;; Made with: wasm-tools parse hello-wasi.wat -o hello-wasi.wasm
(module
  (import "wasi_snapshot_preview1" "fd_write" (func $fd_write (param i32 i32 i32 i32) (result i32)))
  (import "wasi_snapshot_preview1" "proc_exit" (func $exit (param i32)))
  (memory (export "memory") 1)
  (data (i32.const 16) "Hello from WASI, run by Lean\n")
  (func (export "_start")
    ;; One iovec at 0: the text at 16, 29 bytes; the count written goes to 8.
    (i32.store (i32.const 0) (i32.const 16))
    (i32.store (i32.const 4) (i32.const 29))
    (drop (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8)))
    (call $exit (i32.const 0))))
