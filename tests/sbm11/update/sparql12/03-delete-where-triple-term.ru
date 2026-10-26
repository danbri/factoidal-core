PREFIX ex: <http://ex.org/>
# a triple-term pattern with a variable inside: the reference evaluator matches it
DELETE WHERE { ?s ex:says <<( ex:s ex:p ?o )>> }
