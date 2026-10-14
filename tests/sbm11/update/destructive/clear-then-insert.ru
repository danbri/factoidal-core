PREFIX ex: <http://ex.org/>
CLEAR NAMED ; INSERT DATA { GRAPH ex:g1 { ex:a ex:again 1 } } ; DROP GRAPH ex:g1 ; INSERT DATA { GRAPH ex:g1 { ex:a ex:third 3 } }
