;; foaf-check.wat: the FOAF graph's overlap check (LayoutPolicy.checkFootprints and
;; certify, formal/lean4/L4Factoidal/UI/LayoutPolicy.lean) as a WebAssembly kernel.
;; Assembled with wabt `wat2wasm foaf-check.wat` (labs/demos/foafnaut/wasm/build.sh). The
;; proof (formal/lean4/L4Factoidal/WasmVM/Proofs/FoafCheck.lean) is about the assembled
;; bytes, decoded by WasmVM's decoder, not about this text: the assembler is not trusted.
;;
;; check(n, bps, boxes, out) -> certified
;;   boxes: n boxes of four little-endian i32 (left, top, right, bottom), 16 bytes each,
;;          every coordinate in [0, 32768);
;;   out:   n little-endian i32 flags, written: 1 if node i passes, else 0;
;;   result: 1 if every node passes (certify), else 0.
;; Node i passes when its area is positive and 10000 * (sum over j != i of the area of
;; the intersection of box i and box j) <= bps * area.
;; Integer only, no allocator, no imports: the page copies boxes in and flags out.
(module
  (memory (export "memory") 1)
  (func (export "check") (param $n i32) (param $bps i32) (param $boxes i32) (param $out i32) (result i32)
    (local $i i32) (local $j i32) (local $all i32) (local $p i32) (local $ok i32)
    (local $l i64) (local $t i64) (local $r i64) (local $b i64)
    (local $area i64) (local $sum i64) (local $u i64) (local $v i64)
    i32.const 1
    local.set $all
    block
      loop
        local.get $i
        local.get $n
        i32.ge_u
        br_if 1
        ;; p = boxes + 16 i; read box i
        local.get $boxes
        local.get $i
        i32.const 16
        i32.mul
        i32.add
        local.set $p
        local.get $p
        i32.load offset=0
        i64.extend_i32_u
        local.set $l
        local.get $p
        i32.load offset=4
        i64.extend_i32_u
        local.set $t
        local.get $p
        i32.load offset=8
        i64.extend_i32_u
        local.set $r
        local.get $p
        i32.load offset=12
        i64.extend_i32_u
        local.set $b
        ;; area = max(r - l, 0) * max(b - t, 0)
        local.get $r
        local.get $l
        i64.sub
        local.tee $u
        i64.const 0
        local.get $u
        i64.const 0
        i64.gt_s
        select
        local.get $b
        local.get $t
        i64.sub
        local.tee $v
        i64.const 0
        local.get $v
        i64.const 0
        i64.gt_s
        select
        i64.mul
        local.set $area
        i64.const 0
        local.set $sum
        i32.const 0
        local.set $j
        block
          loop
            local.get $j
            local.get $n
            i32.ge_u
            br_if 1
            local.get $j
            local.get $i
            i32.ne
            if
              ;; p = boxes + 16 j
              local.get $boxes
              local.get $j
              i32.const 16
              i32.mul
              i32.add
              local.set $p
              ;; u = max(min(r, rj) - max(l, lj), 0)
              local.get $r
              local.get $p
              i32.load offset=8
              i64.extend_i32_u
              local.tee $u
              local.get $r
              local.get $u
              i64.lt_s
              select
              local.get $l
              local.get $p
              i32.load offset=0
              i64.extend_i32_u
              local.tee $v
              local.get $l
              local.get $v
              i64.gt_s
              select
              i64.sub
              local.tee $u
              i64.const 0
              local.get $u
              i64.const 0
              i64.gt_s
              select
              local.set $u
              ;; v = max(min(b, bj) - max(t, tj), 0)
              local.get $b
              local.get $p
              i32.load offset=12
              i64.extend_i32_u
              local.tee $v
              local.get $b
              local.get $v
              i64.lt_s
              select
              local.get $t
              local.get $p
              i32.load offset=4
              i64.extend_i32_u
              local.tee $v
              local.get $t
              local.get $v
              i64.gt_s
              select
              i64.sub
              local.tee $v
              i64.const 0
              local.get $v
              i64.const 0
              i64.gt_s
              select
              ;; sum += u * v
              local.get $u
              i64.mul
              local.get $sum
              i64.add
              local.set $sum
            end
            local.get $j
            i32.const 1
            i32.add
            local.set $j
            br 0
          end
        end
        ;; ok = (10000 sum <= bps area) if area > 0, else 0
        local.get $sum
        i64.const 10000
        i64.mul
        local.get $bps
        i64.extend_i32_u
        local.get $area
        i64.mul
        i64.le_s
        i32.const 0
        local.get $area
        i64.const 0
        i64.gt_s
        select
        local.set $ok
        ;; out[i] = ok
        local.get $out
        local.get $i
        i32.const 4
        i32.mul
        i32.add
        local.get $ok
        i32.store
        ;; all = ok ? all : 0
        local.get $all
        i32.const 0
        local.get $ok
        select
        local.set $all
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br 0
      end
    end
    local.get $all))
