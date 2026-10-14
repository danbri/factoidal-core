PREFIX ex: <http://ex.org/>
# each operation reads the state the one before left: the second deletes and rewrites what the
# first inserted, the third counts the result with a sub-SELECT
INSERT DATA { ex:x ex:p 1 } ;
DELETE { ?s ex:p ?o } INSERT { ?s ex:p 2 } WHERE { ?s ex:p ?o } ;
INSERT { ex:done ex:count ?c } WHERE { SELECT (COUNT(*) AS ?c) WHERE { ?s ex:p ?o } }
