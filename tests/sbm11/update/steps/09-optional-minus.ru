PREFIX ex: <http://ex.org/>
# OPTIONAL with !BOUND, and MINUS (the reference evaluator)
INSERT { ?s ex:lonely true } WHERE { ?s ex:name ?n OPTIONAL { ?s ex:knows ?k } FILTER(!BOUND(?k)) } ;
DELETE { ?s ex:age ?a } WHERE { ?s ex:age ?a MINUS { ?s ex:name ?n } }
