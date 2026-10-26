PREFIX ex: <http://ex.org/>
# DELETE/INSERT with a FILTER over numeric values of five datatypes (the ids path decides the
# comparison with the reference evaluator on the decoded terms)
DELETE { ?s ex:age ?a } INSERT { ?s ex:years ?a } WHERE { ?s ex:age ?a FILTER(?a > 71) }
