;; wasm-mandelbrot.wat: the module of wasm-mandelbrot.html (the page holds its bytes, made
;; with `wat2wasm wasm-mandelbrot.wat`). The page's script instantiates it with the
;; WebAssembly JavaScript API; Lean runs it in WasmVM, the page's own WebAssembly store.
;;
;; mandel(w, h, x0, y0, step, max) writes one byte per cell into memory at 0, row by row:
;; the iterations before the point x0 + i*step, y0 + j*step leaves the circle of radius 2,
;; or `max` when it stays. It calls the JavaScript import env.row once per row and counts
;; every iteration in the exported global `iterations`.
(module
  (import "env" "row" (func $row (param i32)))
  (memory (export "memory") 1)
  (global $iterations (export "iterations") (mut i32) (i32.const 0))
  (func (export "mandel") (param $w i32) (param $h i32) (param $x0 f64) (param $y0 f64)
                          (param $step f64) (param $max i32)
    (local $i i32) (local $j i32) (local $n i32) (local $p i32)
    (local $cx f64) (local $cy f64) (local $x f64) (local $y f64) (local $t f64)
    (local.set $j (i32.const 0))
    (block $rows (loop $row_loop
      (br_if $rows (i32.ge_u (local.get $j) (local.get $h)))
      (local.set $cy (f64.add (local.get $y0) (f64.mul (f64.convert_i32_u (local.get $j)) (local.get $step))))
      (local.set $i (i32.const 0))
      (block $cols (loop $col_loop
        (br_if $cols (i32.ge_u (local.get $i) (local.get $w)))
        (local.set $cx (f64.add (local.get $x0) (f64.mul (f64.convert_i32_u (local.get $i)) (local.get $step))))
        (local.set $x (f64.const 0)) (local.set $y (f64.const 0)) (local.set $n (i32.const 0))
        (block $esc (loop $iter
          (br_if $esc (i32.ge_u (local.get $n) (local.get $max)))
          (br_if $esc (f64.gt (f64.add (f64.mul (local.get $x) (local.get $x)) (f64.mul (local.get $y) (local.get $y))) (f64.const 4)))
          (local.set $t (f64.add (f64.sub (f64.mul (local.get $x) (local.get $x)) (f64.mul (local.get $y) (local.get $y))) (local.get $cx)))
          (local.set $y (f64.add (f64.mul (f64.mul (f64.const 2) (local.get $x)) (local.get $y)) (local.get $cy)))
          (local.set $x (local.get $t))
          (local.set $n (i32.add (local.get $n) (i32.const 1)))
          (br $iter)))
        (global.set $iterations (i32.add (global.get $iterations) (local.get $n)))
        (i32.store8 (local.get $p) (local.get $n))
        (local.set $p (i32.add (local.get $p) (i32.const 1)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $col_loop)))
      (call $row (local.get $j))
      (local.set $j (i32.add (local.get $j) (i32.const 1)))
      (br $row_loop)))))
