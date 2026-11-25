# String split limit and argument conversion

The pinned Test262 baseline fails three ordinary String split cases on both strict and sloppy execution. Conversion of the limit is observable and comes before string conversion of the separator. An undefined separator with a zero limit produces an empty array. Object separators with an installed Symbol.split method continue through the existing dispatch.

The ordinary path now converts the arguments in specification order, then uses a pure result function. That function returns an empty result for zero before searching the string. The Lean theorem bounds the length of the resulting array by the limit, independently of the string and separator. The argument-conversion order is checked by Test262.

Source: [ECMAScript String.prototype.split](https://tc39.es/ecma262/multipage/text-processing.html#sec-string.prototype.split).
