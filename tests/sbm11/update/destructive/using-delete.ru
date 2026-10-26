PREFIX ex: <http://ex.org/>
DELETE { ?s ex:knows ?o } USING ex:g1 WHERE { ?s ex:knows ?o }
