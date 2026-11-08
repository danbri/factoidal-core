/-
L4Factoidal.WasmVM.Bench.Core: load Factoidal's own Emscripten build of the Lean core
(`l4factoidal.wasm`, from `tools/fetch-builds.sh` or `npm/factoidal-lean/`) into the
engine (https://github.com/danbri/factoidal/issues/1244).

`lake exe wasmvm-bench l4core FILE`: decode, validate, instantiate with stub imports,
then call `__wasm_call_ctors` (export `t`), `l4_init` (`w`) and `l4_version_c` (`x`),
and print the version string that `x` returns. The 18 imports are the Emscripten and
WASI functions named in the build's JavaScript (`var wasmImports = {..}`); the stubs
here are the least each needs: no files but `/dev/urandom` (constant bytes, not
random), no environment, a clock at 0, and `emscripten_resize_heap` grows memory 0.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Bench.Engine

namespace L4Factoidal.WasmVM.Bench.Core
open L4Factoidal.WasmVM

/-- Import field (minified) to the JavaScript function it is in the build. -/
def importNames : List (String × String) :=
  [("a", "_exit"), ("b", "_fd_write"), ("c", "_emscripten_get_now"), ("d", "_fd_read"),
   ("e", "_fd_close"), ("f", "_environ_get"), ("g", "_environ_sizes_get"), ("h", "__abort_js"),
   ("i", "l4_host_size_js"), ("j", "l4_host_read_js"), ("k", "__tzset_js"),
   ("l", "_emscripten_resize_heap"), ("m", "_emscripten_get_heap_max"), ("n", "_fd_seek"),
   ("o", "_fd_fdstat_get"), ("p", "___syscall_openat"), ("q", "_clock_time_get"),
   ("r", "l4_ext_call_js")]

def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 256 + b[i+2]!.toNat * 65536 + b[i+3]!.toNat * 16777216

def le32 (v : Nat) : ByteArray := ⟨#[(v % 256).toUInt8, (v / 256 % 256).toUInt8, (v / 65536 % 256).toUInt8, (v / 16777216 % 256).toUInt8]⟩

/-- The stub host. `names[id]` is the JavaScript name of import `id`; `mem` is the
store address of memory 0. Host calls are counted by name. -/
def host (names : Array String) (mem : Nat) (counts : IO.Ref (Std.HashMap String Nat))
    (id : Nat) (args : Array Value) (st : Store) : IO (Store × HostResult) := do
  let nm := names[id]?.getD s!"import {id}"
  counts.modify fun m => m.insert nm (m.getD nm 0 + 1)
  let i32 := fun (k : Nat) => match args[k]? with | some (.i32 v) => v.toNat | _ => 0
  match nm with
  | "_fd_write" =>
    -- (fd, iov, iovcnt, pnwritten): print the bytes, report them all written.
    let (iov, cnt, pn) := (i32 1, i32 2, i32 3)
    let mut total := 0
    let mut st := st
    for k in [0:cnt] do
      match st.readMem mem (iov + 8 * k) 8 with
      | .ok d =>
        let (p, n) := (u32At d 0, u32At d 4)
        if let .ok bytes := st.readMem mem p n then
          IO.print (String.fromUTF8? bytes |>.getD "<bytes>")
        total := total + n
      | .error _ => pure ()
    if let .ok st' := st.writeMem mem pn (le32 total) then st := st'
    return (st, .values #[.i32 0])
  | "_environ_sizes_get" =>
    let st := (st.writeMem mem (i32 0) (le32 0)).toOption.getD st
    let st := (st.writeMem mem (i32 1) (le32 0)).toOption.getD st
    return (st, .values #[.i32 0])
  | "_environ_get" => return (st, .values #[.i32 0])
  | "_clock_time_get" =>
    -- (clock, precision : i64, ptime): time 0.
    let p := i32 2
    let st := (st.writeMem mem p (le32 0 ++ le32 0)).toOption.getD st
    return (st, .values #[.i32 0])
  | "_emscripten_get_heap_max" => return (st, .values #[.i32 0x80000000])
  | "_emscripten_resize_heap" =>
    let want := i32 0
    let cur := match st.mems[mem]? with | some m => LinearMemory.size m.data | none => 0
    let delta := (want + pageSize - 1) / pageSize - cur / pageSize
    match st.growMem mem delta with
    | some (st, _) => return (st, .values #[.i32 1])
    | none =>
      IO.println s!"  emscripten_resize_heap {want}: refused (memory {cur / pageSize} pages, page limit {st.pageLimit})"
      return (st, .values #[.i32 0])
  | "_emscripten_get_now" => return (st, .values #[.f64 0])
  | "__abort_js" => return (st, .trap "abort")
  | "_exit" => return (st, .exit (i32 0))
  | "__tzset_js" => return (st, .values #[])
  | "___syscall_openat" =>
    -- (dirfd, path, flags, mode): only `/dev/urandom` (the Lean runtime reads it at
    -- start), as fd 3; anything else is ENOENT (44).
    let path := match st.readMem mem (i32 1) 13 with
      | .ok b => String.fromUTF8? b |>.getD ""
      | .error _ => ""
    if path == "/dev/urandom\x00" || path.startsWith "/dev/urandom" then return (st, .values #[.i32 3])
    return (st, .values #[.i32 (UInt32.ofNat (4294967296 - 44))])
  | "_fd_read" =>
    -- (fd, iov, iovcnt, pnread): fd 3 gives bytes 0x5A (not random: a test stub).
    if i32 0 != 3 then return (st, .values #[.i32 8])
    let (iov, cnt, pn) := (i32 1, i32 2, i32 3)
    let mut total := 0
    let mut st := st
    for k in [0:cnt] do
      if let .ok d := st.readMem mem (iov + 8 * k) 8 then
        let (p, n) := (u32At d 0, u32At d 4)
        if let .ok st' := st.writeMem mem p ⟨Array.replicate n 0x5A⟩ then st := st'
        total := total + n
    if let .ok st' := st.writeMem mem pn (le32 total) then st := st'
    return (st, .values #[.i32 0])
  | _ =>
    -- Other WASI calls: EBADF (8); the l4 host hooks: 0.
    let ft := match st.funcs.find? (fun f => match f.kind with | .host i => i == id | _ => false) with
      | some f => f.type | none => ⟨#[], #[]⟩
    let r := if nm.startsWith "_fd" || nm.startsWith "_clock" || nm.startsWith "_environ" then 8 else 0
    return (st, .values (ft.results.map fun t => match t with
      | .i64 => .i64 (UInt64.ofNat r) | .f64 => .f64 0 | .f32 => .f32 0 | _ => .i32 (UInt32.ofNat r)))

def run (path : String) : IO UInt32 := do
  let b ← IO.FS.readBinFile path
  let (r, ns) ← Bench.Engine.timeIt fun _ => Binary.decodeParallel b
  let m ← match r with
    | .ok m => pure m
    | .error e => IO.println s!"decode: {e.toString}"; return 1
  IO.println s!"decode: {m.funcs.size} functions, {m.imports.size} imports, {m.tags.size} tags, {ns / 1000000} ms"
  let (v, ns) ← Bench.Engine.timeIt fun _ => validateParallel m
  let vm ← match v with
    | .ok vm => pure vm
    | .error e => IO.println s!"validate: {e.toString}"; return 1
  let handlers := vm.code.foldl (fun a c => a + (handlersOf c.code).size) 0
  IO.println s!"validate and compile: {ns / 1000000} ms, {handlers} handler-table entries"
  -- Stub imports.
  let mut st0 : Store := {}
  let mut imps : Array ExternVal := #[]
  let mut names : Array String := #[]
  for imp in m.imports do
    match imp.desc with
    | .func t =>
      let (st', a) := st0.addHostFunc (m.types[t]!) names.size
      st0 := st'
      imps := imps.push (.func a)
      names := names.push ((importNames.lookup imp.name).getD s!"{imp.module}.{imp.name}")
    | _ => IO.println s!"import {imp.module}.{imp.name}: not a function, no stub"; return 1
  let (st1, r) := instantiate st0 vm imps
  let ia ← match r with
    | .ok (ia, _) => pure ia
    | .error e => IO.println s!"instantiate: {e.toString}"; return 1
  let some (.mem mem) := st1.export? ia "s" | IO.println "no memory export s"; return 1
  IO.println s!"instantiate: ok, memory {(LinearMemory.size (st1.mems[mem]!).data) / pageSize} pages"
  let counts ← IO.mkRef ({} : Std.HashMap String Nat)
  let lim : Budget := { fuel := 20000000000, run := { maxDepth := 50000, maxSlots := 1 <<< 24 } }
  let mut st := st1
  for (exp, what) in [("t", "__wasm_call_ctors"), ("w", "l4_init"), ("x", "l4_version_c")] do
    let some (.func fa) := st.export? ia exp | IO.println s!"no export {exp}"; return 1
    let t0 ← IO.monoNanosNow
    let (st', o) ← runIO st fa #[] lim (host names mem counts)
    let t1 ← IO.monoNanosNow
    st := st'
    IO.println s!"{what} (export {exp}): {o.describe} in {(t1 - t0) / 1000000} ms"
    match o with
    | .values #[.i32 p] =>
      if exp == "x" && p != 0 then
        match st.readMem mem p.toNat 200 with
        | .ok bytes =>
          let s := (bytes.toList.takeWhile (· != 0)).toArray
          IO.println s!"  version string: {String.fromUTF8? ⟨s⟩ |>.getD "<not UTF-8>"}"
        | .error e => IO.println s!"  read: {e}"
    | .values _ => pure ()
    | _ => break
  let cs ← counts.get
  IO.println s!"host calls: {cs.toList}"
  return 0

end L4Factoidal.WasmVM.Bench.Core
