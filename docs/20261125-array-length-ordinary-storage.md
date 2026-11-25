# 2026-11-25 Length writes on descriptor-backed arrays

Defining an indexed accessor moves an Array from dense storage to ordinary
properties. A subsequent write to its length previously ran through ordinary
data-property assignment and left old indices in place. Array methods that
snapshot length could then read entries that ought to have been deleted.

The length operation for this storage uses the existing own-key order in
reverse and deletes indices until the requested length or the first
non-configurable property. A failed deletion keeps that index and restores
length to one above it. Direct assignment and descriptor writes share the
operation. Conversion runs before reading the current descriptor so the
target can change during either conversion.

[ArraySetLength](https://tc39.es/ecma262/#sec-arraysetlength)
