# Batch 3: one request with two operations. The triple term batch 2 deleted
# comes back; a new directional literal in a triple term in a named graph; and
# a DELETE DATA after them in the same request.
PREFIX ex: <http://ex.org/>
INSERT DATA {
  ex:g ex:says <<( ex:s ex:p "new" )>> .
  GRAPH ex:g2 { ex:j ex:says <<( ex:j ex:p "z"@en--rtl )>> . }
} ;
DELETE DATA {
  ex:h ex:says <<( ex:s ex:p "salaam"@ar--rtl )>> .
}
