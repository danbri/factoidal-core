PREFIX ex: <http://ex.org/>
# USING: the default graph of the WHERE clause is g2 (the reference evaluator over the quads the guard selects)
INSERT { ex:g2 ex:summary ?n } USING ex:g2 WHERE { ?s ex:name ?n }
