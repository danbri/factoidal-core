PREFIX ex: <http://ex.org/>
# the SPARQL 1.2 triple functions in a FILTER and a BIND
DELETE { ?s ex:says ?t } INSERT { ?s ex:said ?o } WHERE { ?s ex:says ?t FILTER(isTRIPLE(?t)) BIND(OBJECT(?t) AS ?o) }
