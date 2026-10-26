PREFIX ex: <http://ex.org/>
INSERT { ex:x ex:p ?o } WHERE { SERVICE <http://localhost:1/sparql> { ?s ?p ?o } }
