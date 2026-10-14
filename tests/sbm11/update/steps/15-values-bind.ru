PREFIX ex: <http://ex.org/>
# VALUES and BIND (the reference evaluator)
INSERT { ?s ex:label ?l } WHERE { VALUES ?s { ex:a ex:b ex:nothere } BIND(CONCAT("n-", STR(?s)) AS ?l) }
