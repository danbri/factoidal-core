PREFIX ex: <http://ex.org/>
# USING NAMED: GRAPH ?g ranges over g1 and g2 only; the template names the graph g3
INSERT { GRAPH ex:g3 { ?s ex:seenIn ?g } } USING NAMED ex:g1 USING NAMED ex:g2 WHERE { GRAPH ?g { ?s ?p ?o } }
