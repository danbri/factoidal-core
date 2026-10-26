PREFIX ex: <http://ex.org/>
INSERT { ?s ex:inAnyGraph ?g } WHERE { GRAPH ?g { ?s ?p ?o } }
