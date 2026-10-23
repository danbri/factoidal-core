PREFIX ex: <http://ex.org/>
# a property path in the WHERE clause (on ids since issue 954)
INSERT { ?x ex:reaches ?y } WHERE { ?x ex:knows+ ?y }
