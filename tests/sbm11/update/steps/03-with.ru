PREFIX ex: <http://ex.org/>
# WITH: the default-graph patterns read g1, the template triples go to g1; the named graph
# patterns of the same WHERE clause read every named graph
WITH ex:g1
DELETE { ?s ex:knows ?o } INSERT { ?o ex:knownBy ?s } WHERE { ?s ex:knows ?o }
