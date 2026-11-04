import L4Factoidal.Rendering.RdfView

namespace L4Factoidal.Rendering.RdfView.Tests
open RDF DOM
private def source := "<https://e.test/alice> <https://e.test/name> \"Alice\"@en .\n<https://e.test/alice> <https://e.test/knows> _:bob .\n_:bob <https://e.test/name> \"Bob\" .\n"
private def graph := (Syntax.parseNTriplesDocument source).toOption.getD []
private def dom := (parse source).toOption.map (·.2)
#guard graph.length == 3
#guard (select {} graph).length == 3
#guard (select {subject := some (.bnode "bob")} graph).length == 1
#guard (select {object := some (.bnode "bob")} graph).length == 1
#guard (select {subject := some (.bnode "absent")} graph).isEmpty
#guard dom.map DOM.Dom.wellFormed == some true
#guard dom.map (fun d => (d.nodes.filter fun n => DOM.Dom.isHtmlElement n "a").size) == some 5
#guard dom.map (fun d => (d.nodes.filter fun n => n.type == .text && n.data == "\"Alice\"@en").size) == some 1
#guard (parse "").toOption.map (fun (_,d) => d.wellFormed) == some true
#guard (parse (source ++ "<https://e.test/s> <https://e.test/p> .")).toOption.isNone
#guard (parse "<relative> <https://e.test/p> <https://e.test/o> .").toOption.isNone
#guard (parse "<https://e.test/s> <https://e.test/p> << <https://e.test/a> <https://e.test/b> <https://e.test/c> >> .").toOption.isNone
private def injection := "<https://e.test/s?x=1&y=2> <https://e.test/p> \"<a href='bad'>literal</a> & text\" ."
private def injectedDom := (parse injection).toOption.map (·.2)
#guard injectedDom.map (fun d => d.wellFormed) == some true
#guard injectedDom.map (fun d => (d.nodes.filter fun n => DOM.Dom.isHtmlElement n "a").size) == some 2
#guard injectedDom.map (fun d => d.nodes.any fun n => n.type == .text && n.data.contains '<') == some true
#guard injectedDom.map (fun d => d.nodes.any fun n => n.attrs.any fun a => a.lname == "href" && a.value == "https://e.test/s?x=1&y=2") == some true
#guard match graph with | t::_ => (toDOM (List.replicate 257 t)).toOption.isNone | [] => false
#guard match graph with | t::_ => (toDOM (List.replicate 256 t)).toOption.isSome | [] => false
#print axioms mem_select
#print axioms predicate_link
end L4Factoidal.Rendering.RdfView.Tests
