PREFIX ex: <http://ex.org/>
INSERT { ?s ex:copy ?o } WHERE { ?s ex:knows ?o FILTER(isIRI(?o)) }
