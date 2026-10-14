PREFIX ex: <http://ex.org/>
# a blank node of the INSERT template is a new node for each solution, the same node in the
# three triples of one solution
INSERT { ?s ex:hasNote _:n . _:n ex:noteOf ?s . _:n ex:text ?name } WHERE { ?s ex:name ?name }
