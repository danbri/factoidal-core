/-
L4Factoidal.HTML.Tests — `#guard` checks of the HTML parser against results
that the WHATWG HTML Living Standard fixes (the adoption agency, implied
tags, foster parenting, foreign content, character references) and against
the parse error reports. Checked when this module is built.
-/
import L4Factoidal.HTML.TreeBuilder

namespace L4Factoidal.HTML.Tests

open L4Factoidal.HTML

def nsTag : NS → String
  | .html => ""
  | .svg => "svg:"
  | .math => "math:"

def showNodes : Nat → List HNode → String
  | 0, _ => ""
  | f + 1, ns => String.join (ns.map fun
    | .text s => s
    | .comment s => "<!--" ++ s ++ "-->"
    | .element ns name attrs kids =>
      "<" ++ nsTag ns ++ name ++ String.join (attrs.map fun a => " " ++ a.1 ++ "=" ++ a.2) ++ ">"
        ++ showNodes f kids ++ "</" ++ name ++ ">")

def render (s : String) : String := showNodes 1000 (parseHtml s).children
def errors (s : String) : Nat := (parseHtml s).errors.size

#guard render "" == "<html></html>" || render "" == "<html><head></head><body></body></html>"
#guard render "<p>Hello" == "<html><head></head><body><p>Hello</p></body></html>"
#guard render "<p>a<p>b" == "<html><head></head><body><p>a</p><p>b</p></body></html>"
#guard render "<ul><li>1<li>2</ul>" == "<html><head></head><body><ul><li>1</li><li>2</li></ul></body></html>"
#guard render "<b><p>x</b>y</p>" == "<html><head></head><body><b></b><p><b>x</b>y</p></body></html>"
#guard render "<a>1<p>2</a>3</p>" == "<html><head></head><body><a>1</a><p><a>2</a>3</p></body></html>"
#guard render "<table><b><tr><td>aaa</td></tr>bbb</table>ccc"
  == "<html><head></head><body><b></b><b>bbb</b><table><tbody><tr><td>aaa</td></tr></tbody></table><b>ccc</b></body></html>"
#guard render "<p>a&amp;&lt;&#65;&#x42;&copy;&notit;&bogus;" == "<html><head></head><body><p>a&<AB©¬it;&bogus;</p></body></html>"
#guard render "<title>a&amp;b</title><script>x<y</script>"
  == "<html><head><title>a&b</title><script>x<y</script></head><body></body></html>"
#guard render "<svg viewbox=1><foreignobject><p>x</p></foreignobject></svg>"
  == "<html><head></head><body><svg:svg viewBox=1><svg:foreignObject><p>x</p></foreignObject></svg></body></html>"
#guard render "<template><p>Hi</template>" == "<html><head><template><p>Hi</p></template></head><body></body></html>"
#guard render "<pre>\nx</pre>" == "<html><head></head><body><pre>x</pre></body></html>"
#guard render "<p id=a id=b>" == "<html><head></head><body><p id=a></p></body></html>"
#guard render "<!--c--><p>x" == "<!--c--><html><head></head><body><p>x</p></body></html>"
#guard errors "<!DOCTYPE html>" == 0
#guard errors "<!DOCTYPE html><title>t</title><p>x" == 0
#guard errors "<p>x" > 0
#guard errors "<!DOCTYPE html><p>x</q>" > 0
#guard errors "<!DOCTYPE html><p id=a id=b>" > 0
#guard errors "<!DOCTYPE html><table><div>x" > 0

end L4Factoidal.HTML.Tests
