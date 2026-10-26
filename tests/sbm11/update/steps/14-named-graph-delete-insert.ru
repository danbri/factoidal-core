PREFIX ex: <http://ex.org/>
# GRAPH in the WHERE clause and in both templates; a graph variable bound to the graph of each solution
DELETE { GRAPH ?g { ?s ex:knows ?o } } INSERT { GRAPH ?g { ?o ex:knownBy2 ?s } } WHERE { GRAPH ?g { ?s ex:knows ?o } }
