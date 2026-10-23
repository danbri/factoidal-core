/-
L4Factoidal.RDF.MediaTypeTests — checks of `RDF/MediaType.lean`, evaluated
during `lake build` (https://github.com/danbri/factoidal/issues/975, hand-over
finding 1).

* Each media type of the six RDF syntaxes gives its format, also with
  parameters and in other letter case (RFC 9110 section 8.3.1: type and
  subtype are case-insensitive).
* A type with no reader here (`text/n3`, `text/plain`) and a format label that
  is not a media type (`turtle`) give no format.
* The file-name extension is used only when the media type is absent; an
  unknown media type does not fall back to the extension.

No executable imports this module.
-/
import L4Factoidal.RDF.MediaType

namespace L4Factoidal.RDF.MediaTypeTests

open L4Factoidal.RDF

#guard formatOfMediaType "text/turtle" == some .turtle
#guard formatOfMediaType "text/turtle; charset=utf-8" == some .turtle
#guard formatOfMediaType "Text/Turtle;charset=UTF-8" == some .turtle
#guard formatOfMediaType "  text/turtle  " == some .turtle
#guard formatOfMediaType "application/n-triples" == some .nt
#guard formatOfMediaType "application/n-triples ; charset=utf-8" == some .nt
#guard formatOfMediaType "application/n-quads" == some .nquads
#guard formatOfMediaType "application/trig" == some .trig
#guard formatOfMediaType "application/rdf+xml" == some .rdfxml
#guard formatOfMediaType "application/ld+json" == some .jsonld
#guard formatOfMediaType "application/ld+json; profile=\"http://www.w3.org/ns/json-ld#expanded\"" == some .jsonld

-- no reader here, or not a registered RDF media type
#guard formatOfMediaType "text/n3" == none
#guard formatOfMediaType "text/plain" == none
#guard formatOfMediaType "application/json" == none
#guard formatOfMediaType "application/x-turtle" == none
-- a format label is not a media type
#guard formatOfMediaType "turtle" == none
#guard formatOfMediaType "" == none
#guard formatOfMediaType "; charset=utf-8" == none

-- every format has a registered media type, and it maps back
#guard [RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].all fun f =>
  formatOfMediaType (mediaTypeOf f) == some f
-- every format has a registered extension, and it maps back
#guard [RdfFormat.nt, .turtle, .nquads, .trig, .rdfxml, .jsonld].all fun f =>
  formatOfRegisteredExtension (registeredExtensionOf f) == some f

-- the extension of the registrations only
#guard formatOfRegisteredExtension ".ttl" == some .turtle
#guard formatOfRegisteredExtension ".TTL" == some .turtle
#guard formatOfRegisteredExtension ".owl" == none
#guard formatOfRegisteredExtension ".xml" == none

-- the media type first; the extension only when the media type is absent
#guard formatOfDocument "text/turtle" "data/x.nq" == some .turtle
#guard formatOfDocument "" "data/x.nq" == some .nquads
#guard formatOfDocument "  " "data/x.trig" == some .trig
#guard formatOfDocument "" "https://ex.org/d.jsonld" == some .jsonld
#guard formatOfDocument "application/x-unknown" "data/x.ttl" == none
#guard formatOfDocument "" "data/x" == none
#guard formatOfDocument "" "data/x.owl" == none

end L4Factoidal.RDF.MediaTypeTests
