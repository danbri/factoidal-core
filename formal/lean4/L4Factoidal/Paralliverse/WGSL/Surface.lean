/-! # Concrete WGSL fragment for a guarded word store

The byte parser accepts two storage declarations, a three-dimensional workgroup
size, the `main` compute signature with `pv_gid` bound to `global_invocation_id`,
and a conditional storage assignment. Word expressions have at most four levels.
The modeled host binds an immutable array at (0,0) and a distinct writable
array at (0,2). An unsupported declaration or out-of-bounds executed operation
has no successful result in this fragment. -/

namespace L4Factoidal.Paralliverse.WGSL.Surface

inductive BufferName where
  | srcWords | dstWords | auxWords
  deriving BEq

inductive Access where
  | read | readWrite
  deriving BEq

structure Binding where
  group : Nat
  slot : Nat
  mode : Access
  name : BufferName

inductive Local where
  | word0 | word1 | bound | index

inductive Expr where
  | literal (value : UInt32)
  | gidX
  | localWord (name : Local)
  | load (name : BufferName) (address : Expr)
  | add (left right : Expr)
  | mul (left right : Expr)

structure Body where
  left : Expr
  right : Expr
  destination : BufferName
  address : Expr
  value : Expr

structure Module where
  first : Binding
  second : Binding
  sizeX : Nat
  sizeY : Nat
  sizeZ : Nat
  body : Body

abbrev Token := List UInt8
abbrev Tokens := List Token
abbrev Parser (α : Type) := Tokens → Option (α × Tokens)

private def spelling (s : String) : Token := s.toUTF8.data.toList

-- Identifiers and numeric literals form maximal words. All other non-whitespace
-- bytes become individual punctuation tokens; the grammar checks their spelling.
private def wordByte (b : UInt8) : Bool :=
  (65 ≤ b && b ≤ 90) || (97 ≤ b && b ≤ 122) || (48 ≤ b && b ≤ 57) || b == 95

private def whitespace (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

private def finishWord (word : Token) (done : Tokens) : Tokens :=
  if word.isEmpty then done else word.reverse :: done

def lex (bytes : ByteArray) : Tokens :=
  let (word, done_) := bytes.data.toList.foldl (fun (acc : Token × Tokens) b =>
    if wordByte b then (b :: acc.1, acc.2)
    else
      let done_ := finishWord acc.1 acc.2
      ([], if whitespace b then done_ else [b] :: done_)) ([], [])
  (finishWord word done_).reverse

def takeToken : Parser Token
  | [] => none
  | t :: rest => some (t, rest)

def expect (words : List String) (ts : Tokens) : Option Tokens :=
  words.foldlM (fun remaining word => do
    let (t, rest) ← takeToken remaining
    if t == spelling word then some rest else none) ts

private def natural (token : Token) : Option Nat := do
  let first :: rest := token | none
  if first == 48 && !rest.isEmpty then none
  else
    token.foldlM (fun value b =>
      if b < 48 || 57 < b then none
      else
        let next := value * 10 + (b.toNat - 48)
        if next < UInt32.size then some next else none) 0

private def number : Parser Nat := fun ts => do
  let (t, rest) ← takeToken ts
  return (← natural t, rest)

private def wordLiteral (t : Token) : Option UInt32 := do
  let suffix :: digits := t.reverse | none
  if suffix == 117 then return UInt32.ofNat (← natural digits.reverse)
  else none

def bufferName (t : Token) : Option BufferName :=
  if t == spelling "src_words" then some .srcWords
  else if t == spelling "dst_words" then some .dstWords
  else if t == spelling "aux_words" then some .auxWords
  else none

def binding : Parser Binding := fun ts => do
  let ts ← expect ["@", "group", "("] ts
  let (group, ts) ← number ts
  let ts ← expect [")", "@", "binding", "("] ts
  let (slot, ts) ← number ts
  let ts ← expect [")", "var", "<", "storage", ","] ts
  let (access, ts) ← takeToken ts
  let mode ← if access == spelling "read" then some Access.read
    else if access == spelling "read_write" then some .readWrite else none
  let ts ← expect [">"] ts
  let (name, ts) ← takeToken ts
  let name ← bufferName name
  let ts ← expect [":", "array", "<", "u32", ">", ";"] ts
  return (⟨group, slot, mode, name⟩, ts)

private def fourLayers {α : Type} (layer : α → α) (bottom : α) : α :=
  layer (layer (layer (layer bottom)))

private def exprLayer (localRef : Token → Option Local) (sub : Parser Expr) : Parser Expr := fun ts => do
  let (t, ts) ← takeToken ts
  if t == spelling "(" then
    let (a, ts) ← sub ts
    let (op, ts) ← takeToken ts
    let (b, ts) ← sub ts
    let ts ← expect [")"] ts
    if op == spelling "+" then return (.add a b, ts)
    else if op == spelling "*" then return (.mul a b, ts)
    else none
  else if t == spelling "pv_gid" then return (.gidX, ← expect [".", "x"] ts)
  else if let some name := bufferName t then
    let ts ← expect ["["] ts
    let (i, ts) ← sub ts
    return (.load name i, ← expect ["]"] ts)
  else if let some name := localRef t then return (.localWord name, ts)
  else return (.literal (← wordLiteral t), ts)

def expressionWith (localRef : Token → Option Local) : Parser Expr :=
  fourLayers (exprLayer localRef) (fun _ => none)

private def expression : Parser Expr := expressionWith (fun _ => none)

def localName (t : Token) : Option Local :=
  if t == spelling "pv_l0" then some .word0
  else if t == spelling "pv_l1" then some .word1
  else if t == spelling "pv_bound" then some .bound
  else if t == spelling "pv_i" then some .index
  else none

private def body : Parser Body := fun ts => do
  let ts ← expect ["if", "("] ts
  let (a, ts) ← expression ts
  let ts ← expect ["<"] ts
  let (b, ts) ← expression ts
  let ts ← expect [")", "{"] ts
  let (name, ts) ← takeToken ts
  let name ← bufferName name
  let ts ← expect ["["] ts
  let (i, ts) ← expression ts
  let ts ← expect ["]", "="] ts
  let (v, ts) ← expression ts
  let ts ← expect [";", "}"] ts
  return (⟨a, b, name, i, v⟩, ts)

def entry : Parser (Nat × Nat × Nat) := fun ts => do
  let ts ← expect ["@", "compute", "@", "workgroup_size", "("] ts
  let (x, ts) ← number ts
  let ts ← expect [","] ts
  let (y, ts) ← number ts
  let ts ← expect [","] ts
  let (z, ts) ← number ts
  if x == 0 || y == 0 || z == 0 then return ← none
  let ts ← expect [")", "fn", "main", "(", "@", "builtin", "(", "global_invocation_id", ")",
    "pv_gid", ":", "vec3", "<", "u32", ">", ")", "{"] ts
  return ((x, y, z), ts)

def distinct (a b : Binding) : Bool :=
  a.name != b.name && (a.group != b.group || a.slot != b.slot)

/-- Parse every byte of the restricted compute module, including declarations and launch attributes. -/
def parseShader (bytes : ByteArray) : Option Module := do
  if bytes.size > 2048 then return ← none
  let (first, ts) ← binding (lex bytes)
  let (second, ts) ← binding ts
  if !distinct first second then return ← none
  let ((x, y, z), ts) ← entry ts
  let (code, ts) ← body ts
  let ts ← expect ["}"] ts
  if ts.isEmpty then return ⟨first, second, x, y, z, code⟩ else none

def Module.lookup (m : Module) (name : BufferName) : Option Binding :=
  if m.first.name == name then some m.first
  else if m.second.name == name then some m.second
  else none

private def evalLayer (readAt : BufferName → UInt32 → Option UInt32) (gid : UInt32) (locals : Local → Option UInt32)
    (sub : Expr → Option UInt32) : Expr → Option UInt32
  | .literal v => some v
  | .gidX => some gid
  | .localWord name => locals name
  | .add a b => do return (← sub a) + (← sub b)
  | .mul a b => do return (← sub a) * (← sub b)
  | .load name address => do
    readAt name (← sub address)

def evalWith (readAt : BufferName → UInt32 → Option UInt32) (gid : UInt32) (locals : Local → Option UInt32) :
    Expr → Option UInt32 :=
  fourLayers (evalLayer readAt gid locals) (fun _ => none)

/-- Word evaluation for every expression depth accepted by the parser. -/
def eval (m : Module) (packet : Array UInt32) (gid : UInt32) : Expr → Option UInt32 :=
  evalWith (fun name address => do
    let decl ← m.lookup name
    if decl.group == 0 && decl.slot == 0 && decl.mode == .read then packet[address.toNat]? else none)
    gid (fun _ => none)

structure Write where
  group : Nat
  slot : Nat
  address : UInt32
  value : UInt32

structure Outcome where
  dst : Array UInt32
  writes : List Write

/-- Interpret the parsed guard, storage binding and operands, retaining the executed store. -/
def run (m : Module) (packet prior : Array UInt32) (gid : UInt32) : Option Outcome := do
  let evalWord := eval m packet gid
  let x ← evalWord m.body.left
  let y ← evalWord m.body.right
  if x < y then
    let d ← m.lookup m.body.destination
    if d.group == 0 && d.slot == 2 && d.mode == .readWrite then
      let i ← evalWord m.body.address
      let v ← evalWord m.body.value
      if h : i.toNat < prior.size then
        return ⟨prior.set i.toNat v h, [⟨d.group, d.slot, i, v⟩]⟩
      else none
    else none
  else return ⟨prior, []⟩

/-- Formal byte-to-invocation meaning. A real WebGPU implementation consumes the WGSL independently. -/
def runText (bytes : ByteArray) (packet prior : Array UInt32) (gid : UInt32) : Option Outcome := do
  let m ← parseShader bytes
  run m packet prior gid

end L4Factoidal.Paralliverse.WGSL.Surface
