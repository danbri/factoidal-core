PREFIX ex: <http://ex.org/>
# a blank node inside a nested triple term; the same label outside it is the same new node
INSERT DATA { ex:k ex:says <<( ex:s ex:p <<( _:x ex:q "1" )>> )>> . _:x ex:label "x" }
