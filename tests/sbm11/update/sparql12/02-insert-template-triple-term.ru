PREFIX ex: <http://ex.org/>
# a triple term in an INSERT template with a variable, and one with a template blank node (a new node for each solution)
INSERT { ?s ex:said <<( ex:s ex:p ?o )>> . ex:n ex:says <<( _:m ex:q ?o )>> } WHERE { ?s ex:knows ?o }
