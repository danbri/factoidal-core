/-
L4Factoidal.EXPath.Catalog — the function SIGNATURES of the EXPath
Binary Module 4.0 (prefix `bin`, namespace http://expath.org/ns/binary)
and the EXPath File Module 4.0 (prefix `file`, namespace
http://expath.org/ns/file), as data in the form of
`XPath4.catalogRaw`.

Generated from `specifications/expath-binary/src/function-catalog.xml`
and `specifications/expath-file/src/function-catalog.xml` of
https://github.com/qt4cg/qtspecs at commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c (2026-10-22): for each
`fos:proto`, the prefix, the local name, the return type and each
parameter's name, type and default, as the specification writes them (one change, marked at
`file:write-binary`). `XPath4.Catalog.catalogExt` adds this table to the XPath 4.0 signature
table; the implementations are `EXPath.Binary.Lib` and
`EXPath.File.Lib`.
-/
namespace L4Factoidal.EXPath

/-- `(prefix, name, return type, [(param, type, default?)])`. -/
def catalogRaw : List (String × String × String × List (String × String × Option String)) := [
  ("bin", "to-octets", "xs:unsignedByte*", [("value", "(xs:hexBinary | xs:base64Binary)", none)]),
  ("bin", "from-octets", "xs:base64Binary", [("values", "xs:unsignedByte*", none)]),
  ("bin", "to-base64url", "xs:string?", [("value", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("bin", "from-base64url", "xs:base64Binary?", [("value", "xs:string?", none)]),
  ("bin", "hex", "xs:base64Binary?", [("value", "xs:string?", none)]),
  ("bin", "bin", "xs:base64Binary?", [("value", "xs:string?", none)]),
  ("bin", "octal", "xs:base64Binary?", [("value", "xs:string?", none)]),
  ("bin", "part", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("offset", "xs:integer", none), ("size", "xs:integer?", some "()")]),
  ("bin", "insert-before", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("offset", "xs:integer", none), ("extra", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("bin", "length", "xs:integer", [("value", "(xs:hexBinary | xs:base64Binary)", none)]),
  ("bin", "join", "xs:base64Binary", [("values", "(xs:hexBinary | xs:base64Binary)*", none)]),
  ("bin", "pad-left", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("count", "xs:integer", none), ("octet", "xs:unsignedByte?", some "0")]),
  ("bin", "pad-right", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("count", "xs:integer", none), ("octet", "xs:unsignedByte?", some "0")]),
  ("bin", "find", "xs:integer?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("offset", "xs:integer", none), ("search", "(xs:hexBinary | xs:base64Binary)", none)]),
  ("bin", "infer-encoding", "record(encoding as xs:string, offset as xs:integer)", [("value", "(xs:hexBinary | xs:base64Binary)", none), ("encoding", "xs:string?", some "()")]),
  ("bin", "decode-string", "xs:string?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("encoding", "xs:string?", some "()"), ("offset", "xs:integer?", some "()"), ("size", "xs:integer?", some "()")]),
  ("bin", "encode-string", "xs:base64Binary?", [("value", "xs:string?", none), ("encoding", "xs:string?", some "'UTF-8'")]),
  ("bin", "pack-integer", "xs:base64Binary", [("value", "xs:integer", none), ("size", "xs:integer", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "unpack-integer", "xs:integer", [("value", "(xs:hexBinary | xs:base64Binary)", none), ("offset", "xs:integer", none), ("size", "xs:integer", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "unpack-unsigned-integer", "xs:integer", [("value", "(xs:hexBinary | xs:base64Binary)", none), ("offset", "xs:integer", none), ("size", "xs:integer", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "unpack-double", "xs:double", [("value", "(xs:hexBinary | xs:base64Binary)", none), ("offset", "xs:integer", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "unpack-float", "xs:float", [("value", "(xs:hexBinary | xs:base64Binary)", none), ("offset", "xs:integer", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "pack-double", "xs:base64Binary", [("value", "xs:double", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "pack-float", "xs:base64Binary", [("value", "xs:float", none), ("order", "enum('least-significant-first', 'little-endian', 'LE', 'most-significant-first', 'big-endian', 'BE')?", some "'most-significant-first'")]),
  ("bin", "or", "xs:base64Binary?", [("value1", "(xs:hexBinary | xs:base64Binary)?", none), ("value2", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("bin", "xor", "xs:base64Binary?", [("value1", "(xs:hexBinary | xs:base64Binary)?", none), ("value2", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("bin", "and", "xs:base64Binary?", [("value1", "(xs:hexBinary | xs:base64Binary)?", none), ("value2", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("bin", "not", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("bin", "shift", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("by", "xs:integer", none)]),
  ("bin", "rotate", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("by", "xs:integer", none)]),
  ("bin", "is-bit-set", "xs:boolean?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("index", "xs:integer", none)]),
  ("bin", "set-bits", "xs:base64Binary?", [("value", "(xs:hexBinary | xs:base64Binary)?", none), ("indices", "xs:integer*", none), ("set", "xs:boolean", none)]),
  ("bin", "count-bits-set", "xs:integer?", [("value", "(xs:hexBinary | xs:base64Binary)?", none)]),
  ("file", "exists", "xs:boolean", [("path", "xs:string", none)]),
  ("file", "is-dir", "xs:boolean", [("path", "xs:string", none)]),
  ("file", "is-file", "xs:boolean", [("path", "xs:string", none)]),
  ("file", "is-absolute", "xs:boolean", [("path", "xs:string", none)]),
  ("file", "last-modified", "xs:dateTime", [("path", "xs:string", none)]),
  ("file", "size", "xs:integer", [("path", "xs:string", none), ("recursive", "xs:boolean?", some "fn:false()")]),
  ("file", "append", "empty-sequence()", [("file", "xs:string", none), ("value", "item()*", none), ("options", "(element(output:serialization-parameters) | map(*))?", some "()")]),
  ("file", "append-binary", "empty-sequence()", [("file", "xs:string", none), ("value", "xs:base64Binary", none)]),
  ("file", "append-text", "empty-sequence()", [("file", "xs:string", none), ("value", "xs:string", none), ("encoding", "xs:string?", some "'UTF-8'")]),
  ("file", "append-text-lines", "empty-sequence()", [("file", "xs:string", none), ("lines", "xs:string*", none), ("encoding", "xs:string?", some "'UTF-8'")]),
  ("file", "copy", "empty-sequence()", [("source", "xs:string", none), ("target", "xs:string", none)]),
  ("file", "create-dir", "empty-sequence()", [("dir", "xs:string", none)]),
  ("file", "create-temp-dir", "xs:string", [("prefix", "xs:string?", some "()"), ("suffix", "xs:string?", some "()"), ("dir", "xs:string?", some "()")]),
  ("file", "create-temp-file", "xs:string", [("prefix", "xs:string?", some "()"), ("suffix", "xs:string?", some "()"), ("dir", "xs:string?", some "()")]),
  ("file", "delete", "empty-sequence()", [("path", "xs:string", none), ("recursive", "xs:boolean?", some "fn:false()")]),
  ("file", "list", "xs:string*", [("dir", "xs:string", none), ("recursive", "xs:boolean?", some "fn:false()"), ("pattern", "xs:string?", some "()")]),
  ("file", "list-roots", "xs:string*", []),
  ("file", "move", "empty-sequence()", [("source", "xs:string", none), ("target", "xs:string", none)]),
  ("file", "read-binary", "xs:base64Binary", [("file", "xs:string", none), ("offset", "xs:integer?", some "0"), ("length", "xs:integer?", some "()")]),
  ("file", "read-text", "xs:string", [("file", "xs:string", none), ("options", "(xs:string | map(*))?", some "()")]),
  ("file", "read-text-lines", "xs:string*", [("file", "xs:string", none), ("options", "(xs:string | map(*))?", some "()")]),
  ("file", "write", "empty-sequence()", [("file", "xs:string", none), ("value", "item()*", none), ("options", "(element(output:serialization-parameters) | map(*))?", some "()")]),
  -- `$offset` defaults to `()`, not `0` as the catalog writes it: the
  -- rules distinguish "if $offset is specified" (overwrite from it) from
  -- the 2-argument form (replace the file), and qt4tests
  -- EXPath-file-writeBinary2-002 expects the replacement.
  ("file", "write-binary", "empty-sequence()", [("file", "xs:string", none), ("value", "xs:base64Binary", none), ("offset", "xs:integer?", some "()")]),
  ("file", "write-text", "empty-sequence()", [("file", "xs:string", none), ("value", "xs:string", none), ("encoding", "xs:string?", some "'UTF-8'")]),
  ("file", "write-text-lines", "empty-sequence()", [("file", "xs:string", none), ("values", "xs:string*", none), ("encoding", "xs:string?", some "'UTF-8'")]),
  ("file", "name", "xs:string", [("path", "xs:string", none)]),
  ("file", "parent", "xs:string?", [("path", "xs:string", none)]),
  ("file", "children", "xs:string*", [("path", "xs:string", none)]),
  ("file", "descendants", "xs:string*", [("path", "xs:string", none), ("options", "map(*)?", some "{}")]),
  ("file", "path-to-native", "xs:string", [("path", "xs:string", none)]),
  ("file", "path-to-uri", "xs:anyURI", [("path", "xs:string", none)]),
  ("file", "resolve-path", "xs:string", [("path", "xs:string", none), ("base", "xs:string?", some "()")]),
  ("file", "dir-separator", "xs:string", []),
  ("file", "line-separator", "xs:string", []),
  ("file", "path-separator", "xs:string", []),
  ("file", "temp-dir", "xs:string", []),
  ("file", "base-dir", "xs:string?", []),
  ("file", "current-dir", "xs:string", [])
]

end L4Factoidal.EXPath
