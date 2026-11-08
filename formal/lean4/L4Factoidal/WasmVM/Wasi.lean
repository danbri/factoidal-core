/-
L4Factoidal.WasmVM.Wasi: a minimal WASI Preview 1 host, deny by default
(https://github.com/danbri/factoidal/issues/1244, https://github.com/danbri/factoidal/issues/1289
section 4; record: docs/designissues/2026-11-07-wasmvm-engine.md, "WASI Preview 1").

Reference: `third_party/wasi/wasi_snapshot_preview1.witx` and `typenames.witx`, from
WebAssembly/WASI at commit 9ea0e7534f46f0c39f28b386fa2becf00923a857 (the last commit
with `legacy/preview1/witx`). Errno values, record layouts and the core Wasm type of
each function follow those files.

- Every one of the 46 `wasi_snapshot_preview1` functions links (`Fn`, `Fn.type`), so
  a module that imports more than it uses still instantiates. An import name that is
  not a Preview 1 function, or a Preview 1 name with another type, is a link error.
- 11 functions do work, and only through a capability record `Caps` that the embedder
  builds in Lean: `args_get`, `args_sizes_get`, `environ_get`, `environ_sizes_get`,
  `clock_res_get`, `clock_time_get`, `random_get`, `fd_write` (fd 1 and 2, to sinks
  the embedder gives), `fd_fdstat_get` (fd 0 to 2), `proc_exit`, `sched_yield`.
- The other 35 answer an errno and do nothing else: `EBADF` for the `fd_*` functions
  (no file descriptor beyond 0 to 2 exists, and 0 to 2 grant only `fd_write`),
  `ENOTCAPABLE` for `path_*` and `sock_*`, `ENOSYS` for `poll_oneoff` and `proc_raise`.
- `Caps` has no field for files, directories or sockets. The empty record `{}` grants
  nothing: no arguments, no environment, no clock, no randomness, no output.

The host is generic in its monad `m`: it can do nothing but what the `Caps` functions
do. `denied_is_pure` proves that each of the 35 is `pure` of its errno in every monad,
for every capability record, argument list and store: no effect, no change to the
store, never success. `host_path_open` lifts this to the host function set that `link`
builds. A function `Caps` grants nothing to also never succeeds
(`fd_write_needs_sink`, `random_get_needs_source`, `clock_time_get_needs_clock`).
-/
import L4Factoidal.WasmVM.Api

namespace L4Factoidal.WasmVM.Wasi
open L4Factoidal.WasmVM

def moduleName : String := "wasi_snapshot_preview1"

/-- `$errno` (typenames.witx: an enum with tag u16; the value is the position in the
list). The values used here. -/
abbrev Errno := UInt16

namespace Errno
def success : Errno := 0
def badf : Errno := 8
def fault : Errno := 21
def inval : Errno := 28
def io : Errno := 29
def nosys : Errno := 52
def notcapable : Errno := 76
end Errno

/-- `$filetype` `character_device` (typenames.witx, enum tag u8). -/
def filetypeCharacterDevice : UInt8 := 2
/-- `$rights` bit `fd_write` (typenames.witx, flags u64: bit 6). -/
def rightFdWrite : UInt64 := 64

/-- The functions of `wasi_snapshot_preview1`, in the order of the witx file. -/
inductive Fn where
  | args_get | args_sizes_get | environ_get | environ_sizes_get
  | clock_res_get | clock_time_get
  | fd_advise | fd_allocate | fd_close | fd_datasync | fd_fdstat_get | fd_fdstat_set_flags
  | fd_fdstat_set_rights | fd_filestat_get | fd_filestat_set_size | fd_filestat_set_times
  | fd_pread | fd_prestat_get | fd_prestat_dir_name | fd_pwrite | fd_read | fd_readdir
  | fd_renumber | fd_seek | fd_sync | fd_tell | fd_write
  | path_create_directory | path_filestat_get | path_filestat_set_times | path_link
  | path_open | path_readlink | path_remove_directory | path_rename | path_symlink
  | path_unlink_file
  | poll_oneoff | proc_exit | proc_raise | sched_yield | random_get
  | sock_accept | sock_recv | sock_send | sock_shutdown
  deriving DecidableEq, Repr, Inhabited

namespace Fn

def all : List Fn :=
  [args_get, args_sizes_get, environ_get, environ_sizes_get, clock_res_get, clock_time_get,
   fd_advise, fd_allocate, fd_close, fd_datasync, fd_fdstat_get, fd_fdstat_set_flags,
   fd_fdstat_set_rights, fd_filestat_get, fd_filestat_set_size, fd_filestat_set_times,
   fd_pread, fd_prestat_get, fd_prestat_dir_name, fd_pwrite, fd_read, fd_readdir,
   fd_renumber, fd_seek, fd_sync, fd_tell, fd_write,
   path_create_directory, path_filestat_get, path_filestat_set_times, path_link,
   path_open, path_readlink, path_remove_directory, path_rename, path_symlink,
   path_unlink_file,
   poll_oneoff, proc_exit, proc_raise, sched_yield, random_get,
   sock_accept, sock_recv, sock_send, sock_shutdown]

/-- The export name in the witx file. -/
def name : Fn → String
  | args_get => "args_get" | args_sizes_get => "args_sizes_get"
  | environ_get => "environ_get" | environ_sizes_get => "environ_sizes_get"
  | clock_res_get => "clock_res_get" | clock_time_get => "clock_time_get"
  | fd_advise => "fd_advise" | fd_allocate => "fd_allocate" | fd_close => "fd_close"
  | fd_datasync => "fd_datasync" | fd_fdstat_get => "fd_fdstat_get"
  | fd_fdstat_set_flags => "fd_fdstat_set_flags" | fd_fdstat_set_rights => "fd_fdstat_set_rights"
  | fd_filestat_get => "fd_filestat_get" | fd_filestat_set_size => "fd_filestat_set_size"
  | fd_filestat_set_times => "fd_filestat_set_times" | fd_pread => "fd_pread"
  | fd_prestat_get => "fd_prestat_get" | fd_prestat_dir_name => "fd_prestat_dir_name"
  | fd_pwrite => "fd_pwrite" | fd_read => "fd_read" | fd_readdir => "fd_readdir"
  | fd_renumber => "fd_renumber" | fd_seek => "fd_seek" | fd_sync => "fd_sync"
  | fd_tell => "fd_tell" | fd_write => "fd_write"
  | path_create_directory => "path_create_directory" | path_filestat_get => "path_filestat_get"
  | path_filestat_set_times => "path_filestat_set_times" | path_link => "path_link"
  | path_open => "path_open" | path_readlink => "path_readlink"
  | path_remove_directory => "path_remove_directory" | path_rename => "path_rename"
  | path_symlink => "path_symlink" | path_unlink_file => "path_unlink_file"
  | poll_oneoff => "poll_oneoff" | proc_exit => "proc_exit" | proc_raise => "proc_raise"
  | sched_yield => "sched_yield" | random_get => "random_get"
  | sock_accept => "sock_accept" | sock_recv => "sock_recv" | sock_send => "sock_send"
  | sock_shutdown => "sock_shutdown"

def ofName? (s : String) : Option Fn := all.find? (·.name == s)

/-- The core Wasm parameter types, as the witx lowering gives them: a pointer, `$size`,
`$fd` and every 32-bit or smaller integer is i32; `$filesize`, `$timestamp`, `$rights`,
`$dircookie` and `$filedelta` are i64; a `string` is two i32 (pointer, length); an
`expected` result with a value is an extra i32 pointer for the value. -/
def params : Fn → List ValType
  | args_get | args_sizes_get | environ_get | environ_sizes_get => [.i32, .i32]
  | clock_res_get => [.i32, .i32]
  | clock_time_get => [.i32, .i64, .i32]
  | fd_advise => [.i32, .i64, .i64, .i32]
  | fd_allocate => [.i32, .i64, .i64]
  | fd_close | fd_datasync | fd_sync => [.i32]
  | fd_fdstat_get | fd_fdstat_set_flags | fd_filestat_get | fd_prestat_get | fd_tell => [.i32, .i32]
  | fd_fdstat_set_rights => [.i32, .i64, .i64]
  | fd_filestat_set_size => [.i32, .i64]
  | fd_filestat_set_times => [.i32, .i64, .i64, .i32]
  | fd_pread | fd_pwrite => [.i32, .i32, .i32, .i64, .i32]
  | fd_prestat_dir_name => [.i32, .i32, .i32]
  | fd_read | fd_write => [.i32, .i32, .i32, .i32]
  | fd_readdir => [.i32, .i32, .i32, .i64, .i32]
  | fd_renumber => [.i32, .i32]
  | fd_seek => [.i32, .i64, .i32, .i32]
  | path_create_directory | path_remove_directory | path_unlink_file => [.i32, .i32, .i32]
  | path_filestat_get => [.i32, .i32, .i32, .i32, .i32]
  | path_filestat_set_times => [.i32, .i32, .i32, .i32, .i64, .i64, .i32]
  | path_link => [.i32, .i32, .i32, .i32, .i32, .i32, .i32]
  | path_open => [.i32, .i32, .i32, .i32, .i32, .i64, .i64, .i32, .i32]
  | path_readlink => [.i32, .i32, .i32, .i32, .i32, .i32]
  | path_rename => [.i32, .i32, .i32, .i32, .i32, .i32]
  | path_symlink => [.i32, .i32, .i32, .i32, .i32]
  | poll_oneoff => [.i32, .i32, .i32, .i32]
  | proc_exit | proc_raise => [.i32]
  | sched_yield => []
  | random_get => [.i32, .i32]
  | sock_accept => [.i32, .i32, .i32]
  | sock_recv => [.i32, .i32, .i32, .i32, .i32, .i32]
  | sock_send => [.i32, .i32, .i32, .i32, .i32]
  | sock_shutdown => [.i32, .i32]

/-- The core Wasm type. Every function gives an i32 errno, except `proc_exit`, which
does not return. -/
def type (f : Fn) : FuncType :=
  ⟨f.params.toArray, if f == proc_exit then #[] else #[.i32]⟩

/-- The 11 functions that do work, each through `Caps`. -/
def isGranted : Fn → Bool
  | args_get | args_sizes_get | environ_get | environ_sizes_get | clock_res_get
  | clock_time_get | random_get | fd_write | fd_fdstat_get | proc_exit | sched_yield => true
  | _ => false

/-- The errno of a function that is not granted. -/
def denyErrno : Fn → Errno
  | poll_oneoff | proc_raise => Errno.nosys
  | path_create_directory | path_filestat_get | path_filestat_set_times | path_link
  | path_open | path_readlink | path_remove_directory | path_rename | path_symlink
  | path_unlink_file | sock_accept | sock_recv | sock_send | sock_shutdown => Errno.notcapable
  | _ => Errno.badf

theorem all_length : all.length = 46 := rfl
theorem all_names_distinct : (all.map name).Nodup := by decide
theorem ofName?_name (f : Fn) : ofName? f.name = some f := by cases f <;> rfl
theorem granted_count : (all.filter isGranted).length = 11 := rfl

end Fn

/-- The capability record. The embedder builds it in Lean; the WASI host can do
nothing that its functions do not do. There is no field for files, directories or
sockets: this host never grants them. `{}` grants nothing. -/
structure Caps (m : Type → Type) where
  /-- `args_get`: the program's arguments (the first is by custom the program name). -/
  args : Array String := #[]
  /-- `environ_get`: `KEY=VALUE` strings. -/
  env : Array String := #[]
  /-- `clock_time_get`: the action that reads clock `id` (0 realtime, 1 monotonic,
  2 process CPU time, 3 thread CPU time), in nanoseconds; `none`: not granted. -/
  clock : UInt32 → Option (m UInt64) := fun _ => none
  /-- `clock_res_get`: the resolution of clock `id` in nanoseconds; `none`: not granted. -/
  clockRes : UInt32 → Option UInt64 := fun _ => none
  /-- `random_get`: `n` bytes. The embedder chooses the source: `IO.getRandomBytes`
  for real randomness, or a fixed seed in a test that says so. `none`: not granted. -/
  random : Option (Nat → m ByteArray) := none
  /-- `fd_write` to fd 1: where the bytes go (capture into a buffer, or forward). -/
  stdout : Option (ByteArray → m Unit) := none
  /-- `fd_write` to fd 2. -/
  stderr : Option (ByteArray → m Unit) := none

section
variable {M : Type} [LinearMemory M] {m : Type → Type} [Monad m]

def le32 (v : Nat) : ByteArray :=
  ⟨#[(v % 256).toUInt8, (v / 256 % 256).toUInt8, (v / 65536 % 256).toUInt8, (v / 16777216 % 256).toUInt8]⟩
def le64 (v : UInt64) : ByteArray := le32 (v.toNat % 4294967296) ++ le32 (v.toNat / 4294967296)
def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 256 + b[i+2]!.toNat * 65536 + b[i+3]!.toNat * 16777216

/-- Argument `k` as an unsigned i32 (a pointer, size, fd or enum value). -/
def arg32 (args : Array Value) (k : Nat) : Nat :=
  match args[k]? with | some (.i32 v) => v.toNat | _ => 0

def put (mem : Nat) (st : StoreOf M) (off : Nat) (bytes : ByteArray) : Except Errno (StoreOf M) :=
  (st.writeMem mem off bytes).mapError fun _ => Errno.fault
def get (mem : Nat) (st : StoreOf M) (off n : Nat) : Except Errno ByteArray :=
  (st.readMem mem off n).mapError fun _ => Errno.fault
def fits (mem : Nat) (st : StoreOf M) (off n : Nat) : Bool :=
  match st.mems[mem]? with
  | some mi => off + n ≤ LinearMemory.size mi.data
  | none => false

def errno (st : StoreOf M) (e : Errno) : StoreOf M × HostResult := (st, .values #[.i32 e.toUInt32])

/-- Write `bytes` at `off` and answer success, or `fault` when they do not fit. The
store is never held twice, so the write is in place (`StoreOf.writeMemS`). -/
def answerPut (mem : Nat) (st : StoreOf M) (off : Nat) (bytes : ByteArray) : StoreOf M × HostResult :=
  match st.writeMemS mem off bytes with
  | (st, true) => errno st Errno.success
  | (st, false) => errno st Errno.fault

/-- The answer of a step that only writes memory. -/
def answer (st : StoreOf M) : Except Errno (StoreOf M) → StoreOf M × HostResult
  | .ok st' => errno st' Errno.success
  | .error e => errno st e

/-- `*_sizes_get`: the count, and the bytes of all strings with a NUL after each. -/
def strSizes (strs : Array String) : Nat × Nat :=
  (strs.size, strs.foldl (fun n s => n + s.utf8ByteSize + 1) 0)

/-- `args_get`, `environ_get`: pointer `k` at `ptrs + 4k`, the strings (NUL-ended) one
after another from `buf`. -/
def putStrings (mem : Nat) (st : StoreOf M) (ptrs buf : Nat) (strs : Array String) :
    Except Errno (StoreOf M) := do
  let mut st := st
  let mut off := buf
  for (s, k) in strs.zipIdx do
    let b := s.toUTF8.push 0
    st ← put mem st (ptrs + 4 * k) (le32 off)
    st ← put mem st off b
    off := off + b.size
  return st

def putSizes (mem : Nat) (st : StoreOf M) (pCount pBytes : Nat) (strs : Array String) :
    Except Errno (StoreOf M) := do
  let (n, bytes) := strSizes strs
  let st ← put mem st pCount (le32 n)
  put mem st pBytes (le32 bytes)

/-- The bytes of a `$ciovec_array` (`iovs`, `n` entries of pointer and length). -/
def gather (mem : Nat) (st : StoreOf M) (iovs n : Nat) : Except Errno ByteArray := do
  let mut out := ByteArray.empty
  for k in [0:n] do
    let d ← get mem st (iovs + 8 * k) 8
    out := out ++ (← get mem st (u32At d 0) (u32At d 4))
  return out

/-- `$fdstat` (typenames.witx; C layout, 24 bytes): `fs_filetype` u8 at 0,
`fs_flags` u16 at 2, `fs_rights_base` u64 at 8, `fs_rights_inheriting` u64 at 16. -/
def fdstat (filetype : UInt8) (rightsBase : UInt64) : ByteArray :=
  ⟨#[filetype, 0, 0, 0, 0, 0, 0, 0]⟩ ++ le64 rightsBase ++ le64 0

/-- The sink of fd 1 or 2. -/
def sinkOf (caps : Caps m) (fd : Nat) : Option (ByteArray → m Unit) :=
  if fd == 1 then caps.stdout else if fd == 2 then caps.stderr else none

/-- `fd_write(fd, iovs, iovs_len, nwritten)`. -/
def fdWrite (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M) :
    m (StoreOf M × HostResult) :=
  let fd := arg32 args 0
  if fd == 0 || fd > 2 then pure (errno st Errno.badf) else
  match sinkOf caps fd with
  | none => pure (errno st Errno.notcapable)
  | some write =>
    match gather mem st (arg32 args 1) (arg32 args 2) with
    | .error e => pure (errno st e)
    | .ok bytes =>
      match st.writeMemS mem (arg32 args 3) (le32 bytes.size) with
      | (st, false) => pure (errno st Errno.fault)
      | (st, true) => do write bytes; pure (errno st Errno.success)

/-- `clock_time_get(id, precision, ptime)`. The precision is a hint; it is not used. -/
def clockTimeGet (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M) :
    m (StoreOf M × HostResult) :=
  let id := arg32 args 0
  if id > 3 then pure (errno st Errno.inval) else
  match caps.clock id.toUInt32 with
  | none => pure (errno st Errno.notcapable)
  | some read => do
    let t ← read
    pure (answerPut mem st (arg32 args 2) (le64 t))

/-- `random_get(buf, buf_len)`. -/
def randomGet (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M) :
    m (StoreOf M × HostResult) :=
  match caps.random with
  | none => pure (errno st Errno.notcapable)
  | some gen =>
    let (buf, n) := (arg32 args 0, arg32 args 1)
    if !fits mem st buf n then pure (errno st Errno.fault) else do
    let bytes ← gen n
    if bytes.size != n then pure (errno st Errno.io)
    else pure (answerPut mem st buf bytes)

/-- One call of WASI function `f` with the memory at store address `mem`. -/
def call (caps : Caps m) (mem : Nat) (f : Fn) (args : Array Value) (st : StoreOf M) :
    m (StoreOf M × HostResult) :=
  match f with
  | .args_sizes_get => pure (answer st (putSizes mem st (arg32 args 0) (arg32 args 1) caps.args))
  | .args_get => pure (answer st (putStrings mem st (arg32 args 0) (arg32 args 1) caps.args))
  | .environ_sizes_get => pure (answer st (putSizes mem st (arg32 args 0) (arg32 args 1) caps.env))
  | .environ_get => pure (answer st (putStrings mem st (arg32 args 0) (arg32 args 1) caps.env))
  | .clock_res_get =>
    let id := arg32 args 0
    if id > 3 then pure (errno st Errno.inval) else
    match caps.clockRes id.toUInt32 with
    | none => pure (errno st Errno.notcapable)
    | some r => pure (answerPut mem st (arg32 args 1) (le64 r))
  | .clock_time_get => clockTimeGet caps mem args st
  | .random_get => randomGet caps mem args st
  | .fd_write => fdWrite caps mem args st
  | .fd_fdstat_get =>
    let fd := arg32 args 0
    if fd > 2 then pure (errno st Errno.badf) else
    let rights := if fd != 0 && (sinkOf caps fd).isSome then rightFdWrite else 0
    pure (answerPut mem st (arg32 args 1) (fdstat filetypeCharacterDevice rights))
  | .proc_exit => pure (st, .exit (arg32 args 0))
  | .sched_yield => pure (errno st Errno.success)
  | f => pure (errno st f.denyErrno)

/-! ## Linking -/

/-- What an import is bound to. -/
inductive Binding where
  | wasi (f : Fn)
  /-- An import of another module, served by the embedder's own function. -/
  | extra (module name : String)
  deriving DecidableEq, Repr, Inhabited

/-- Resolve one import of `md`. A `wasi_snapshot_preview1` import must name a Preview 1
function with its witx type; another import must be one that `extra` accepts. -/
def resolve (extra : String → String → Bool) (md : Module) (imp : Import) : Except String Binding :=
  match imp.desc with
  | .func t =>
    let ft := md.types[t]?.getD ⟨#[], #[]⟩
    if imp.module == moduleName then
      match Fn.ofName? imp.name with
      | none => .error s!"import {imp.module}.{imp.name}: not a WASI Preview 1 function"
      | some f =>
        if ft == f.type then .ok (.wasi f)
        else .error s!"import {imp.module}.{imp.name}: type {repr ft} is not the witx type {repr f.type}"
    else if extra imp.module imp.name then .ok (.extra imp.module imp.name)
    else .error s!"import {imp.module}.{imp.name}: no host function"
  | _ => .error s!"import {imp.module}.{imp.name}: only function imports are served"

/-- Bind every import of `md`: one host function per import, with the import's index
as its host id. Gives the store, the extern values for `instantiate`, and the
bindings for `host`. -/
def link (st : StoreOf M) (md : Module) (extra : String → String → Bool := fun _ _ => false) :
    Except String (StoreOf M × Array ExternVal × Array Binding) := do
  let bs ← md.imports.mapM (resolve extra md)
  let (st, ex) := md.imports.zipIdx.foldl (init := (st, (#[] : Array ExternVal))) fun (st, ex) (imp, i) =>
    let ft := match imp.desc with | .func t => md.types[t]?.getD ⟨#[], #[]⟩ | _ => ⟨#[], #[]⟩
    let (st, a) := st.addHostFunc ft i
    (st, ex.push (.func a))
  return (st, ex, bs)

/-- The host function set: host id `id` runs its binding. `extra` serves the
embedder's own imports. -/
def host (caps : Caps m) (mem : Nat) (bs : Array Binding)
    (extra : String → String → Array Value → StoreOf M → m (StoreOf M × HostResult))
    (id : Nat) (args : Array Value) (st : StoreOf M) : m (StoreOf M × HostResult) :=
  match bs[id]? with
  | some (.wasi f) => call caps mem f args st
  | some (.extra mo n) => extra mo n args st
  | none => pure (st, .trap s!"no host function {id}")

/-! ## Deny by default -/

/-- A function that is not granted answers its errno and does nothing else: in every
monad, for every capability record, memory, argument list and store, the call is
`pure` of the unchanged store and the errno. So it runs no action of `Caps` (and the
host has no other action to run), writes no memory, and never succeeds. -/
theorem denied_is_pure (caps : Caps m) (mem : Nat) (f : Fn) (h : f.isGranted = false)
    (args : Array Value) (st : StoreOf M) :
    call caps mem f args st = pure (st, .values #[.i32 f.denyErrno.toUInt32]) := by
  cases f <;> first | rfl | simp [Fn.isGranted] at h

theorem denyErrno_ne_success (f : Fn) : f.denyErrno ≠ Errno.success := by
  cases f <;> decide

/-- `path_open` never opens anything: `ENOTCAPABLE`, nothing else. -/
theorem path_open_denied (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M) :
    call caps mem .path_open args st = pure (st, .values #[.i32 Errno.notcapable.toUInt32]) :=
  denied_is_pure caps mem .path_open rfl args st

/-- No `fd_*` function reads: `fd_read` and `fd_pread` answer `EBADF`. -/
theorem fd_read_denied (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M) :
    call caps mem .fd_read args st = pure (st, .values #[.i32 Errno.badf.toUInt32]) ∧
    call caps mem .fd_pread args st = pure (st, .values #[.i32 Errno.badf.toUInt32]) :=
  ⟨rfl, rfl⟩

/-- The `path_*` and `sock_*` functions (the test exe checks that these are exactly
the names with those prefixes). -/
def pathSock : List Fn :=
  [.path_create_directory, .path_filestat_get, .path_filestat_set_times, .path_link,
   .path_open, .path_readlink, .path_remove_directory, .path_rename, .path_symlink,
   .path_unlink_file, .sock_accept, .sock_recv, .sock_send, .sock_shutdown]

/-- Every `path_*` and `sock_*` function is denied with `ENOTCAPABLE`. -/
theorem path_sock_denied : ∀ f ∈ pathSock, f.isGranted = false ∧ f.denyErrno = Errno.notcapable := by
  decide

/-- 35 of the 46 functions are denied. -/
theorem denied_count : (Fn.all.filter (!·.isGranted)).length = 35 := rfl

/-- At the level of the host function set that `link` builds: an import bound to
`path_open` answers `ENOTCAPABLE`, whatever the capabilities and the embedder's
other functions. -/
theorem host_path_open (caps : Caps m) (mem : Nat) (bs : Array Binding)
    (extra : String → String → Array Value → StoreOf M → m (StoreOf M × HostResult))
    (id : Nat) (h : bs[id]? = some (.wasi .path_open)) (args : Array Value) (st : StoreOf M) :
    host caps mem bs extra id args st = pure (st, .values #[.i32 Errno.notcapable.toUInt32]) := by
  simp only [host, h]; exact path_open_denied caps mem args st

/-- `resolve` binds a `wasi_snapshot_preview1` import only to the Preview 1 function
of the same name, never to the embedder's `extra` functions. -/
theorem resolve_wasi (extra : String → String → Bool) (md : Module) (imp : Import) (b : Binding)
    (hm : imp.module = moduleName) (h : resolve extra md imp = .ok b) :
    ∃ f, b = .wasi f ∧ Fn.ofName? imp.name = some f := by
  unfold resolve at h
  split at h
  · simp only [hm, beq_self_eq_true, if_true] at h
    split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h; exact ⟨f, rfl, hf⟩
      · cases h
  · cases h

/-- With no output sink, `fd_write` never succeeds and writes nothing. -/
theorem fd_write_needs_sink (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M)
    (h1 : caps.stdout = none) (h2 : caps.stderr = none) :
    ∃ e, e ≠ Errno.success ∧ call caps mem .fd_write args st = pure (st, .values #[.i32 e.toUInt32]) := by
  show ∃ e, e ≠ Errno.success ∧ fdWrite caps mem args st = _
  have hs : ∀ fd, sinkOf caps fd = none := by intro fd; simp [sinkOf, h1, h2]
  simp only [fdWrite, hs]
  split
  · exact ⟨Errno.badf, by decide, rfl⟩
  · exact ⟨Errno.notcapable, by decide, rfl⟩

/-- With no random source, `random_get` never succeeds and writes nothing. -/
theorem random_get_needs_source (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M)
    (h : caps.random = none) :
    call caps mem .random_get args st = pure (st, .values #[.i32 Errno.notcapable.toUInt32]) := by
  simp only [call, randomGet, h]; rfl

/-- With no clock, `clock_time_get` never succeeds and writes nothing. -/
theorem clock_time_get_needs_clock (caps : Caps m) (mem : Nat) (args : Array Value) (st : StoreOf M)
    (h : ∀ id, caps.clock id = none) :
    ∃ e, e ≠ Errno.success ∧ call caps mem .clock_time_get args st = pure (st, .values #[.i32 e.toUInt32]) := by
  show ∃ e, e ≠ Errno.success ∧ clockTimeGet caps mem args st = _
  simp only [clockTimeGet, h]
  split
  · exact ⟨Errno.inval, by decide, rfl⟩
  · exact ⟨Errno.notcapable, by decide, rfl⟩

end
end L4Factoidal.WasmVM.Wasi
