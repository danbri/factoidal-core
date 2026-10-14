PREFIX ex: <http://ex.org/>
# a property path in the WHERE clause (the reference evaluator)
INSERT { ?x ex:reaches ?y } WHERE { ?x ex:knows+ ?y }
