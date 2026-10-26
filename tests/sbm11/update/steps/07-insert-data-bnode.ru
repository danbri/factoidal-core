PREFIX ex: <http://ex.org/>
# a blank node label of INSERT DATA is one new node: the same node in two graphs.
# A second operation has its own label: the parser refuses a label that two
# INSERT DATA operations share (SPARQL 1.1 Update section 19.6).
INSERT DATA { _:a ex:p 1 . _:a ex:q _:b . GRAPH ex:g3 { _:a ex:r 2 . _:b ex:r 3 } } ;
INSERT DATA { _:c ex:s 4 }
