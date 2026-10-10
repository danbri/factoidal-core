(* sparql_trailing_values_unit.ml — pins the behaviours fixed for the
   w3c/rdf-tests ec2ba15 move (2026-10-10), each with a positive case and a
   negative case, so an engine that answers yes (or no) for everything fails.

   A. Language tags compare case-insensitively under `=` (RDF 1.1 Concepts
      3.3; W3C functions/strlang04).
   B. The trailing VALUES clause of a query that groups is joined AFTER
      grouping and HAVING (SPARQL 1.1 18.2.4.3). The grouped-SELECT cases
      below give a different answer under the old join-before-grouping order:
      a group is paired with each compatible VALUES row, and its aggregates
      are computed over the group alone.
   C. ASK reads GROUP BY, HAVING, OFFSET and LIMIT (grammar rule 12);
      CONSTRUCT orders before it slices and reads GROUP BY and HAVING
      (16.2, 18.4); both accept a trailing VALUES clause.
   D. ORDER BY in a grouped SELECT runs before projection, so it can name a
      group variable the projection drops (15.1).
   E. A SELECT expression may not assign a variable that the trailing VALUES
      clause binds (W3C syntax-query group-by-values-scope-03), and a
      variable the trailing VALUES clause binds may be projected from a
      grouped query (scope-01, scope-02).
   F. Protocol 2.2.4: using-graph-uri / using-named-graph-uri in the query
      string of a direct sparql-update POST conflict with USING or WITH.
   G. XMLLiteral content is Exclusive XML Canonicalization: namespace
      declarations where a prefix is visibly utilized (xml-canon-test001,
      -002; rdfms-xml-literal-namespaces-test001).
   H. D-entailment: "10"^^xsd:integer entails "10.0"^^xsd:decimal
      (rdf-mt datatypes-semantic-equivalence-between-datatypes). *)

let passed = ref 0
let failed = ref 0

let check ~name expected actual =
  if String.equal expected actual then begin
    incr passed;
    Printf.printf "  PASS  %s\n" name
  end else begin
    incr failed;
    Printf.printf "  FAIL  %s: expected %S got %S\n" name expected actual
  end

let prefix = "PREFIX : <http://example.org/> "
let data_ttl =
  "@prefix : <http://example.org/> .\n\
   :a :p 1 .\n:a :p 5 .\n:b :p 2 .\n"
let empty_ds = RDF_Graph_Executable.({ ds_default = []; ds_named = [] })
let graph = Parser_Turtle.parse_turtle data_ttl

let parse q =
  match SPARQL11_Parser.parse_sparql (prefix ^ q) with
  | SPARQL11_Parser.ParseOk (query, _) -> Ok query
  | SPARQL11_Parser.ParseErr m -> Error m

let show_term (t : RDF_Graph_Executable.rdf_term) =
  match t with
  | RDF_Graph_Executable.T_IRI i ->
    let n = String.length i in
    let cut = try String.rindex i '/' + 1 with Not_found -> 0 in
    String.sub i cut (n - cut)
  | RDF_Graph_Executable.T_Literal l ->
    l.RDF_Graph_Executable.lexical_form
  | RDF_Graph_Executable.T_BNode b -> "_:" ^ b
  | _ -> "?"

let show_row row =
  row
  |> List.sort (fun (a, _) (b, _) -> compare a b)
  |> List.map (fun (v, t) -> v ^ "=" ^ show_term t)
  |> String.concat ","

let select q =
  match parse q with
  | Error m -> "PARSE-ERROR: " ^ m
  | Ok query ->
    SPARQL11_Algebra.eval_select_query query graph empty_ds
    |> List.map show_row |> String.concat " | "

let select_sorted q =
  match parse q with
  | Error m -> "PARSE-ERROR: " ^ m
  | Ok query ->
    SPARQL11_Algebra.eval_select_query query graph empty_ds
    |> List.map show_row |> List.sort compare |> String.concat " | "

let ask q =
  match parse q with
  | Error m -> "PARSE-ERROR: " ^ m
  | Ok query -> string_of_bool (SPARQL11_Algebra.eval_ask_query query graph empty_ds)

let construct q =
  match parse q with
  | Error m -> "PARSE-ERROR: " ^ m
  | Ok query ->
    SPARQL11_Algebra.eval_construct_query query graph empty_ds
    |> List.map (fun (t : RDF_Graph_Executable.triple) ->
         (match t.RDF_Graph_Executable.s with
          | RDF_Graph_Executable.S_IRI i -> show_term (RDF_Graph_Executable.T_IRI i)
          | RDF_Graph_Executable.S_BNode b -> "_:" ^ b)
         ^ " " ^ show_term t.RDF_Graph_Executable.o)
    |> List.sort compare |> String.concat " | "

let is_parse_error q = match parse q with Error _ -> "error" | Ok _ -> "ok"

let () =
  (* A. language tags *)
  check ~name:"A1 \"abc\"@en = \"abc\"@EN is true" "r=true"
    (select "SELECT ((\"abc\"@en = \"abc\"@EN) AS ?r) {}");
  check ~name:"A2 STRLANG(\"abc\",\"EN\") = \"abc\"@en is true" "r=true"
    (select "SELECT ((STRLANG(\"abc\", \"EN\") = \"abc\"@en) AS ?r) {}");
  check ~name:"A3 \"abc\"@en = \"abd\"@EN is false (different lexical form)" "r=false"
    (select "SELECT ((\"abc\"@en = \"abd\"@EN) AS ?r) {}");
  check ~name:"A4 \"abc\"@en != \"abc\"@EN is false" "r=false"
    (select "SELECT ((\"abc\"@en != \"abc\"@EN) AS ?r) {}");
  check ~name:"A5 \"abc\"@en = \"abc\"@fr is false (different tag)" "r=false"
    (select "SELECT ((\"abc\"@en = \"abc\"@fr) AS ?r) {}");

  (* B. VALUES after grouping *)
  check ~name:"B1 group paired with each compatible VALUES row; aggregate over the group alone"
    "c=2,s=a,x=1 | c=2,s=a,x=2"
    (select "SELECT ?s ?x (COUNT(*) AS ?c) WHERE { ?s :p ?o } GROUP BY ?s VALUES (?s ?x) { (:a 1) (:a 2) }");
  check ~name:"B2 a group with no compatible VALUES row is dropped"
    ""
    (select "SELECT ?s (COUNT(*) AS ?c) WHERE { ?s :p ?o } GROUP BY ?s VALUES ?s { :z }");
  check ~name:"B3 without VALUES the same query keeps both groups"
    "c=1,s=b | c=2,s=a"
    (select_sorted "SELECT ?s (COUNT(*) AS ?c) WHERE { ?s :p ?o } GROUP BY ?s");
  check ~name:"B4 a VALUES variable is visible to a SELECT expression"
    "s=a,w=7 | s=b,w=7"
    (select_sorted "SELECT ?s (STR(?v) AS ?w) WHERE { ?s :p ?o } GROUP BY ?s VALUES ?v { 7 }");

  (* C. ASK and CONSTRUCT *)
  check ~name:"C1 ASK with a trailing VALUES clause that matches" "true"
    (ask "ASK { ?s :p ?o } VALUES ?o { 1 }");
  check ~name:"C2 ASK with a trailing VALUES clause that does not match" "false"
    (ask "ASK { ?s :p ?o } VALUES ?o { 99 }");
  check ~name:"C3 ASK LIMIT 0 is false" "false" (ask "ASK { ?s :p ?o } LIMIT 0");
  check ~name:"C4 ASK LIMIT 1 is true" "true" (ask "ASK { ?s :p ?o } LIMIT 1");
  check ~name:"C5 ASK OFFSET past the last solution is false" "false"
    (ask "ASK { ?s :p ?o } OFFSET 3");
  check ~name:"C6 ASK GROUP BY with a HAVING that no group meets is false" "false"
    (ask "ASK { ?s :p ?o } GROUP BY ?s HAVING (COUNT(*) > 2)");
  check ~name:"C7 ASK GROUP BY with a HAVING that one group meets is true" "true"
    (ask "ASK { ?s :p ?o } GROUP BY ?s HAVING (COUNT(*) > 1)");
  check ~name:"C8 CONSTRUCT orders before it slices"
    "b 2"
    (construct "CONSTRUCT { ?s :rank ?r } WHERE { ?s :p ?o } ORDER BY DESC(?s) LIMIT 1 VALUES (?s ?r) { (:a 1) (:b 2) }");
  check ~name:"C9 CONSTRUCT ascending picks the other solution"
    "a 1"
    (construct "CONSTRUCT { ?s :rank ?r } WHERE { ?s :p ?o } ORDER BY ?s LIMIT 1 VALUES (?s ?r) { (:a 1) (:b 2) }");
  check ~name:"C10 CONSTRUCT GROUP BY: only group variables and VALUES variables are in scope"
    "a 1 | a 2"
    (construct "CONSTRUCT { ?s :n ?x . ?s :m ?o } WHERE { ?s :p ?o } GROUP BY ?s VALUES (?s ?x) { (:a 1) (:a 2) }");
  check ~name:"C11 CONSTRUCT HAVING keeps the groups that pass"
    "a 2"
    (construct "CONSTRUCT { ?s :n ?c } WHERE { ?s :p ?o } GROUP BY ?s HAVING (COUNT(*) > 1) VALUES ?c { 2 }");

  (* D. ORDER BY before projection in a grouped SELECT *)
  check ~name:"D1 ORDER BY DESC on a dropped group variable" "c=1 | c=2"
    (select "SELECT (COUNT(*) AS ?c) WHERE { ?s :p ?o } GROUP BY ?s ORDER BY DESC(?s)");
  check ~name:"D2 ORDER BY ASC on the same variable" "c=2 | c=1"
    (select "SELECT (COUNT(*) AS ?c) WHERE { ?s :p ?o } GROUP BY ?s ORDER BY ?s");

  (* E. scope rules *)
  check ~name:"E1 projecting a VALUES variable from a grouped query parses" "ok"
    (is_parse_error "SELECT ?s ?v { ?s :p ?o } GROUP BY ?s VALUES ?v { 1 }");
  check ~name:"E2 the same projection without the VALUES clause is rejected" "error"
    (is_parse_error "SELECT ?s ?v { ?s :p ?o } GROUP BY ?s");
  check ~name:"E3 a SELECT expression of a VALUES variable parses" "ok"
    (is_parse_error "SELECT ?s (STR(?v) AS ?w) { ?s :p ?o } GROUP BY ?s VALUES ?v { 1 }");
  check ~name:"E4 assigning a variable that the trailing VALUES binds is rejected" "error"
    (is_parse_error "SELECT ?s (COUNT(*) AS ?c) { ?s :p ?o } GROUP BY ?s VALUES ?c { 0 1 2 }");
  check ~name:"E5 assigning a different variable is accepted" "ok"
    (is_parse_error "SELECT ?s (COUNT(*) AS ?c) { ?s :p ?o } GROUP BY ?s VALUES ?d { 0 1 2 }");
  check ~name:"E6 a bare ASK LIMIT is rejected" "error" (is_parse_error "ASK { ?s :p ?o } LIMIT");
  check ~name:"E8 ORDER BY accepts a built-in call such as LCASE" "ok"
    (is_parse_error "SELECT ?s { ?s :p ?o } ORDER BY LCASE(STR(?s))");
  check ~name:"E9 an aggregate with a plain variable and no GROUP BY is rejected" "error"
    (is_parse_error "SELECT (COUNT(*) AS ?c) ?s { ?s :p ?o }");
  check ~name:"E7 VALUES after a CONSTRUCT template query parses" "ok"
    (is_parse_error "CONSTRUCT { ?s :q ?o } WHERE { ?s :p ?o } VALUES ?o { 1 }");

  (* F. Protocol 2.2.4 *)
  let decode ct qs body =
    match SPARQL_Protocol.decode_request "POST" "/sparql/" qs ct body with
    | SPARQL_Protocol.PR_Bad _ -> "bad"
    | SPARQL_Protocol.PR_Update _ -> "update"
    | SPARQL_Protocol.PR_Query _ -> "query" in
  check ~name:"F1 using-named-graph-uri with WITH is a 4xx" "bad"
    (decode "application/sparql-update" "using-named-graph-uri=http%3A%2F%2Fex%2Fg"
       "WITH <http://ex/g> DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }");
  check ~name:"F2 using-graph-uri with USING is a 4xx" "bad"
    (decode "application/sparql-update" "using-graph-uri=http%3A%2F%2Fex%2Fg"
       "DELETE { ?s ?p ?o } USING <http://ex/h> WHERE { ?s ?p ?o }");
  check ~name:"F3 using-named-graph-uri without WITH or USING is accepted" "update"
    (decode "application/sparql-update" "using-named-graph-uri=http%3A%2F%2Fex%2Fg"
       "DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }");
  check ~name:"F4 WITH without a using parameter is accepted" "update"
    (decode "application/sparql-update" ""
       "WITH <http://ex/g> DELETE { ?s ?p ?o } WHERE { ?s ?p ?o }");

  (* G. Exclusive XML Canonicalization of rdf:XMLLiteral *)
  let literal_of rdfxml =
    let triples = Parser_RDFXML.parse_rdfxml_with_base "http://example.com/doc.rdf" rdfxml in
    match triples with
    | [t] ->
      (match t.RDF_Graph_Executable.o with
       | RDF_Graph_Executable.T_Literal l -> l.RDF_Graph_Executable.lexical_form
       | _ -> "not a literal")
    | l -> Printf.sprintf "%d triples" (List.length l) in
  let doc body =
    "<?xml version=\"1.0\"?>\n\
     <rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n\
     \         xmlns:eg=\"http://example.org/\">\n\
     <rdf:Description rdf:about=\"http://www.example.org/a\">\n" ^ body ^
    "\n</rdf:Description>\n</rdf:RDF>\n" in
  check ~name:"G1 an empty element that uses no prefix carries no declaration"
    "<br></br>"
    (literal_of (doc "<eg:prop rdf:parseType=\"Literal\"><br /></eg:prop>"));
  check ~name:"G2 an element that uses a document prefix carries that declaration"
    "<eg:x xmlns:eg=\"http://example.org/\"></eg:x>"
    (literal_of (doc "<eg:prop rdf:parseType=\"Literal\"><eg:x/></eg:prop>"));
  check ~name:"G3 a child under a declaring parent repeats nothing"
    "<eg:x xmlns:eg=\"http://example.org/\"><eg:y></eg:y></eg:x>"
    (literal_of (doc "<eg:prop rdf:parseType=\"Literal\"><eg:x><eg:y/></eg:x></eg:prop>"));
  check ~name:"G4 a prefix the document never declared is not invented"
    "<other:x></other:x>"
    (literal_of (doc "<eg:prop rdf:parseType=\"Literal\"><other:x/></eg:prop>"));
  check ~name:"G5 rdfms-xml-literal-namespaces-test001: default and prefixed declarations"
    "\n      <html:h1 xmlns:html=\"http://NoHTML.example.org\">\n        <b xmlns=\"http://www.w3.org/1999/xhtml\">John</b>\n      </html:h1>\n   "
    (literal_of
       "<?xml version=\"1.0\"?>\n\
        <rdf:RDF xmlns=\"http://www.w3.org/1999/xhtml\"\n\
        \   xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n\
        \   xmlns:html=\"http://NoHTML.example.org\"\n\
        \   xmlns:my=\"http://my.example.org/\">\n\
        \   <rdf:Description rdf:about=\"http://example.org/John_Smith\">\n\
        \    <my:Name rdf:parseType=\"Literal\">\n\
        \      <html:h1>\n\
        \        <b>John</b>\n\
        \      </html:h1>\n\
        \   </my:Name>\n\
        \  </rdf:Description>\n\
        </rdf:RDF>\n");

  (* H. D-entailment across xsd:integer and xsd:decimal *)
  let ttl s = Parser_Turtle.parse_turtle
      ("@prefix : <http://example.org/> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\n" ^ s) in
  check ~name:"H1 \"10\"^^xsd:integer entails \"10.0\"^^xsd:decimal" "true"
    (string_of_bool (RDF_Entailment_Regime.entails_rdf
       (ttl ":a :b \"10\"^^xsd:integer .") (ttl ":a :b \"10.0\"^^xsd:decimal .")));
  check ~name:"H2 \"10\"^^xsd:integer does not entail \"11.0\"^^xsd:decimal" "false"
    (string_of_bool (RDF_Entailment_Regime.entails_rdf
       (ttl ":a :b \"10\"^^xsd:integer .") (ttl ":a :b \"11.0\"^^xsd:decimal .")));
  check ~name:"H3 \"10\"^^xsd:integer does not entail the string \"10.0\"" "false"
    (string_of_bool (RDF_Entailment_Regime.entails_rdf
       (ttl ":a :b \"10\"^^xsd:integer .") (ttl ":a :b \"10.0\" .")));

  Printf.printf "sparql_trailing_values_unit: %d pass, %d fail (out of %d)\n"
    !passed !failed (!passed + !failed);
  if !failed > 0 then exit 1
