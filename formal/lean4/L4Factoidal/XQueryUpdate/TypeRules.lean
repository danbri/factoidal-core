/-
L4Factoidal.XQueryUpdate.TypeRules — operand checks for the Static
Typing Feature of XQuery Update Facility 3.0, §5.1–§5.6:
https://www.w3.org/TR/xquery-update-30/.

The caller supplies inferred sequence types in the operand order of
XQueryUpdate.Grammar. This module depends only on XPath4.Core, so that
XPath4's static analysis can call it without importing XQuery evaluation.
The checks use sequence-type inclusion, including occurrence indicators.
Content types account for atomic-to-text conversion and document-node
flattening in the enclosed-expression rules of XQuery 3.0 §3.9.1.3.

IType records choices and cardinalities, rather than ordered concatenation.
Consequently an insertion source that can contain both attributes and
other nodes cannot establish the required attribute-prefix order here.
Static typing tracking: https://github.com/danbri/factoidal/issues/1177.
-/
import L4Factoidal.XPath4.Core

namespace L4Factoidal.XQueryUpdate

open XPath4

/-- XQuery Update 3.0 §5.1: node kinds allowed before or after a target. -/
private def childKinds : IType :=
  .choice [.elem none, .text, .comment, .pi none]

/-- XQuery Update 3.0 §5.1: `into` accepts elements or documents. -/
private def intoKinds : IType := .choice [.elem none, .doc none]

/-- XQuery Update 3.0 §5.3: replace targets also include attributes. -/
private def replaceKinds : IType :=
  .choice [.elem none, .attr none, .text, .comment, .pi none]

/-- XQuery Update 3.0 §5.4: only named node kinds can be renamed. -/
private def renameKinds : IType :=
  .choice [.elem none, .attr none, .pi none]

/-- XQuery Update 3.0 §5.1 and XQuery 3.0 §3.9.1.3: content that becomes
    non-attribute nodes after document flattening and atomic text creation. -/
private def contentKinds : IType :=
  .choice [.elem none, .text, .comment, .pi none, .doc none,
    .atomic (.b .anyAtomicType)]

/-- XQuery Update 3.0 §5.1: the source has a provable attribute-prefix
    order if all its items are attributes, all become child nodes, or
    there is at most one item of either kind. -/
private def insertionSourceOk (t : IType) : Bool :=
  subtype t (.seq (.attr none) .star) || subtype t (.seq contentKinds .star) ||
    subtype t (.seq (.choice [.attr none, contentKinds]) .opt)

/-- XQuery Update 3.0 §5.4: the atomized new name is exactly one string,
    untyped atomic value, or QName. Node operands use their typed value;
    annotation-specific atomization remains the inference caller's task. -/
private def renameNameOk (t : IType) : Bool :=
  subtype t (.choice [.atomic (.b .string), .atomic .untyped,
    .atomic (.b .qname)])

/-- Check XQuery Update Facility 3.0 §5.1–§5.6 operand types.
    `ts` follows the grammar's operand order; the first string of `ss`
    carries the insertion position (`into`, `first`, `last`, `before`,
    `after`). Optional targets retain the dynamic empty-target check.
    Copy sources must have exactly one node. Unrelated extension tags
    have no update operand constraints. -/
def checkOperandTypes (tag : String) (ts : List IType) (ss : List String) : M Unit := do
  match tag, ts with
  | "upd-insert", [src, tgt] =>
    if !insertionSourceOk src then
      err "XUTY0004" "the insertion source type does not establish an attribute prefix followed by child content"
    let into := ["into", "first", "last"].contains (ss.headD "into")
    if into then
      if !subtype tgt (.seq intoKinds .opt) then
        err "XUTY0005" "insert into requires an optional element or document target"
      if !subtype src (.seq contentKinds .star) &&
          !subtype tgt (.seq (.elem none) .opt) then
        err "XUTY0022" "an insertion source containing attributes requires an element target"
    else if !subtype tgt (.seq childKinds .opt) then
      err "XUTY0006" "insert before or after requires an optional element, text, comment or processing-instruction target"
  | "upd-delete", [tgt] =>
    if !subtype tgt (.seq .anyNode .star) then
      err "XUTY0007" "delete requires a sequence of nodes"
  | "upd-replace", [tgt, replacement] =>
    if !subtype tgt (.seq replaceKinds .opt) then
      err "XUTY0008" "replace requires an optional element, attribute, text, comment or processing-instruction target"
    if !subtype tgt (.seq (.attr none) .opt) &&
        !subtype replacement (.seq contentKinds .star) then
      err "XUTY0010" "a non-attribute replacement target requires child content"
    if !subtype tgt (.seq childKinds .opt) &&
        !subtype replacement (.seq (.attr none) .star) then
      err "XUTY0011" "an attribute replacement target requires attributes"
  | "upd-replace-value", [tgt, _] =>
    if !subtype tgt (.seq replaceKinds .opt) then
      err "XUTY0008" "replace value requires an optional element, attribute, text, comment or processing-instruction target"
  | "upd-rename", [tgt, name] =>
    if !subtype tgt (.seq renameKinds .opt) then
      err "XUTY0012" "rename requires an optional element, attribute or processing-instruction target"
    if !renameNameOk name then
      err "XPTY0004" "the new name must atomize to exactly one string, untyped atomic value or QName"
  | "upd-copy", [src] =>
    if !subtype src .anyNode then
      err "XUTY0013" "copy requires exactly one node"
  | _, _ => pure ()

/-- The error-code observation used below for XQuery Update 3.0 §5 tests. -/
private def operandErrorCode : M Unit → Option String
  | .ok _ => none
  | .error e => some e.code

-- XQuery Update 3.0 §5.1: accepted source types and insertion positions.
#guard (checkOperandTypes "upd-insert" [.elem none, .elem none] []).isOk
#guard (checkOperandTypes "upd-insert" [.attr none, .elem none] ["first"]).isOk
#guard (checkOperandTypes "upd-insert" [.text, .doc none] ["last"]).isOk
#guard (checkOperandTypes "upd-insert" [.doc none, .elem none] ["before"]).isOk
#guard (checkOperandTypes "upd-insert" [.atomic (.b .integer), .elem none] ["after"]).isOk
#guard (checkOperandTypes "upd-insert" [.empty, .seq (.elem none) .opt] []).isOk
#guard (checkOperandTypes "upd-insert" [.seq (.choice [.attr none, .elem none]) .opt,
    .elem none] []).isOk
#guard (checkOperandTypes "upd-insert" [.elemT none untypedQN false,
    .doc (some (.elem none))] []).isOk
#guard (operandErrorCode (checkOperandTypes "upd-insert" [.seq .anyNode .star, .elem none] [])) == some "XUTY0004"
#guard (checkOperandTypes "upd-insert" [.seq (.choice [.elem none, .attr none]) .plus,
    .elem none] []).toOption.isNone
#guard (operandErrorCode (checkOperandTypes "upd-insert" [.elem none, .seq (.elem none) .star] [])) == some "XUTY0005"
#guard (operandErrorCode (checkOperandTypes "upd-insert" [.elem none, .attr none] ["after"])) == some "XUTY0006"
#guard (operandErrorCode (checkOperandTypes "upd-insert" [.attr none, .doc none] [])) == some "XUTY0022"

-- XQuery Update 3.0 §5.2–§5.3: optional specific targets and broad node types.
#guard (checkOperandTypes "upd-delete" [.seq .anyNode .star] []).isOk
#guard (checkOperandTypes "upd-delete" [.empty] []).isOk
#guard (operandErrorCode (checkOperandTypes "upd-delete" [.seq .item .star] [])) == some "XUTY0007"
#guard (checkOperandTypes "upd-replace" [.seq (.elem none) .opt, .text] []).isOk
#guard (checkOperandTypes "upd-replace" [.seq (.attr none) .opt, .attr none] []).isOk
#guard (checkOperandTypes "upd-replace" [.elem none, .empty] []).isOk
#guard (operandErrorCode (checkOperandTypes "upd-replace" [.seq .anyNode .opt, .empty] [])) == some "XUTY0008"
#guard (operandErrorCode (checkOperandTypes "upd-replace" [.elem none, .seq .anyNode .star] [])) == some "XUTY0010"
#guard (operandErrorCode (checkOperandTypes "upd-replace" [.attr none, .seq .anyNode .star] [])) == some "XUTY0011"
#guard (operandErrorCode (checkOperandTypes "upd-replace" [.elem none, .attr none] [])) == some "XUTY0010"
#guard (operandErrorCode (checkOperandTypes "upd-replace" [.attr none, .elem none] [])) == some "XUTY0011"
#guard (checkOperandTypes "upd-replace-value" [.attr none, .atomic (.b .integer)] []).isOk
#guard (operandErrorCode (checkOperandTypes "upd-replace-value" [.seq (.elem none) .star, .text] [])) == some "XUTY0008"

-- XQuery Update 3.0 §5.4–§5.6: named targets, name types and copy cardinality.
#guard (checkOperandTypes "upd-rename" [.pi none, .atomic (.b .string)] []).isOk
#guard (checkOperandTypes "upd-rename" [.attr none, .atomic (.b .qname)] []).isOk
#guard (checkOperandTypes "upd-rename" [.attrT none untypedAtomicQN, .atomic .untyped] []).isOk
#guard (operandErrorCode (checkOperandTypes "upd-rename" [.comment, .atomic (.b .string)] [])) == some "XUTY0012"
#guard (operandErrorCode (checkOperandTypes "upd-rename" [.attr none, .atomic (.b .duration)] [])) == some "XPTY0004"
#guard (checkOperandTypes "upd-copy" [.anyNode] []).isOk
#guard (checkOperandTypes "upd-copy" [.elem none] []).isOk
#guard (operandErrorCode (checkOperandTypes "upd-copy" [.seq (.elem none) .star] [])) == some "XUTY0013"
#guard (operandErrorCode (checkOperandTypes "upd-copy" [.item] [])) == some "XUTY0013"

end L4Factoidal.XQueryUpdate
