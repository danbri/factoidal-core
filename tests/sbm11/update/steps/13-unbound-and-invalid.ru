PREFIX ex: <http://ex.org/>
# a template triple with an unbound variable, a literal subject or a literal predicate is
# dropped (section 3.1.3.2); the other triples of the template stay
DELETE { ?s ex:years ?a . ?a ex:literalSubject ?s . ?s ?unbound ?a } INSERT { ?a ex:literalSubject ?s . ?s ex:copied ?a . ?s ex:unboundHere ?nothing } WHERE { ?s ex:years ?a }
