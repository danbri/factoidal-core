import L4Factoidal.XProc31.Core
import L4Factoidal.XPath4.Uri

namespace L4Factoidal.XProc31

/-- Form components use UTF-8 percent encoding; spaces alone become plus.
The existing URI encoder supplies byte encoding and uppercase hex digits. -/
def encodeFormComponent (text : String) : String :=
  (Fn.String.pctEncodeWith (fun c =>
    (c.toNat < 128 && c.isAlphanum) || "*-._".contains c) text).replace "%20" "+"

def decodeForm (text : String) : List (XPath4.Atomic × XPath4.Seq) := Id.run do
  let mut entries : List (XPath4.Atomic × XPath4.Seq) := []
  for pair in text.splitOn "&" do
    if pair.isEmpty then continue
    let parts := pair.splitOn "="
    let key := XPath4.uriDecode true (parts.headD "")
    let value := XPath4.sStr (XPath4.uriDecode true (String.intercalate "=" parts.tail))
    if entries.any (fun (k,_) => k.str == key) then
      entries := entries.map (fun (k,v) => (k,if k.str == key then v ++ value else v))
    else entries := entries ++ [(XPath4.Atomic.ofStr key,value)]
  pure entries

def encodeForm (entries : List (XPath4.Atomic × XPath4.Seq)) : Result String := do
  let parts ← entries.mapM fun (key,values) => do
    if !key.isStringLike then error "XD0036" "form parameter keys must be strings" else pure ()
    values.mapM fun value => match value with
      | .atom atom =>
        if !atom.isStringLike then error "XD0036" "form parameter values must be strings"
        else pure (encodeFormComponent key.str ++ "=" ++ encodeFormComponent atom.str)
      | _ => error "XD0036" "form parameter values must be strings"
  pure (String.intercalate "&" parts.flatten)

def formStep (step : XML.Node) (env : XPath4.Env) : Result (List Document) := do
  if tag step == "www-form-urldecode" then
    let text ← option step "value" env
    pure [{node := .text "", contentType := "application/json", value := some [.map (decodeForm text)]}]
  else
    let parameters ← match (named step "with-option").find? (fun n => attr n "name" == "parameters") with
      | some opt => eval (attr opt "select") env
      | none => eval (attr step "parameters" "map{}") env
    let [.map entries] := parameters | error "XD0036" "form parameters must be a map"
    pure [{node := .text (← encodeForm entries), contentType := "text/plain"}]

#guard encodeFormComponent "ä +&=" == "%C3%A4+%2B%26%3D"
#guard (decodeForm "a=one&a=two&bare&=x=y").map (fun (k,v) => (k.str,v.length)) ==
  [("a",2),("bare",1),("",1)]
#guard (encodeForm (decodeForm "x=%C3%A4+%2B&x=two")).toOption == some "x=%C3%A4+%2B&x=two"
#guard (decodeForm "&&").isEmpty

end L4Factoidal.XProc31
