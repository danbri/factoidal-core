# Batch 2: DELETE DATA of triple-term quads: one of the base, one batch 1
# added, a directional literal batch 1 added, and a nested one of a named
# graph of the base.
PREFIX ex: <http://ex.org/>
DELETE DATA {
  ex:b ex:says <<( ex:s ex:p ex:o )>> .
  ex:g ex:says <<( ex:s ex:p "new" )>> .
  ex:h ex:label "hello"@en--ltr .
  GRAPH ex:g2 { ex:f ex:says <<( ex:u ex:p <<( ex:v ex:q ex:w )>> )>> . }
}
