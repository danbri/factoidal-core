# Batch 1: INSERT DATA with RDF 1.2 terms (issue 792 item 1). A triple term the
# base dictionary holds, a new one, a new one nested three deep, directional
# literals, a triple term with a directional literal, and a nested triple term
# in a named graph.
PREFIX ex: <http://ex.org/>
INSERT DATA {
  ex:g ex:says <<( ex:s ex:p "x"@en )>> .
  ex:g ex:says <<( ex:s ex:p "new" )>> .
  ex:g ex:says <<( ex:u ex:p <<( ex:v ex:q <<( ex:w ex:r "deeper"@de )>> )>> )>> .
  ex:h ex:label "marhaba"@ar--rtl .
  ex:h ex:label "hello"@en--ltr .
  ex:h ex:says <<( ex:s ex:p "salaam"@ar--rtl )>> .
  ex:h ex:says <<( ex:h ex:label "hello"@en--ltr )>> .
  GRAPH ex:g3 { ex:i ex:says <<( ex:s ex:p <<( ex:t ex:q "deep"@fr )>> )>> . }
}
