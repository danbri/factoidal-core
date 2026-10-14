PREFIX ex: <http://ex.org/>
# a WHERE clause with no solution changes nothing; an empty WHERE clause has one solution
DELETE WHERE { ?s ex:neverThere ?o } ;
INSERT { ex:empty ex:solution _:fresh } WHERE { }
