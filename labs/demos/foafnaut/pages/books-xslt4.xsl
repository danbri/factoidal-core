<?xml version="1.0" encoding="UTF-8"?>
<!-- XSLT 4 in a browser: each card is one XSLT 4.0 or XPath 4.0 feature, run by Lean.
     The expression cards are run as written, with xsl:evaluate, so the code shown is the code run. -->
<xsl:stylesheet version="4.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
 xmlns:xs="http://www.w3.org/2001/XMLSchema" xmlns:map="http://www.w3.org/2005/xpath-functions/map"
 xmlns:array="http://www.w3.org/2005/xpath-functions/array" xmlns:f="urn:foafnaut:xslt4" xmlns:err="http://www.w3.org/2005/xqt-errors"
 exclude-result-prefixes="#all" expand-text="yes">
 <xsl:output method="html"/>

 <!-- A named record type: a constructor function f:summary(title, year) comes with it. -->
 <xsl:record-type name="f:summary">
  <xsl:field name="title" as="xs:string"/>
  <xsl:field name="year" as="xs:integer"/>
 </xsl:record-type>

 <xsl:variable name="status" select="map { 'read': '#2d7d4f', 'reading': '#c47d12', 'wish': '#7a5cb8' }"/>
 <xsl:variable name="ratings" select="parse-json(/library/ratings)"/>

 <!-- Expression cards: [section, feature, what it is, code]. -->
 <xsl:variable name="cards" as="array(xs:string)*" expand-text="no" select="
  ['Maps and arrays', 'map:build', 'Group items into a map, one key for each group.',
   'map:build(book, fn { @status }) => map:for-each(fn($k, $v) { `{$k}: {count($v)}` })'],
  ['Maps and arrays', 'Ordered maps', 'A map keeps its keys in the order they were added.',
   'map { ''z'': 1, ''a'': 2, ''m'': 3 } => map:keys()'],
  ['Maps and arrays', 'Arrays', 'array { } makes one member for each item.',
   'array { book ! xs:integer(@pages) } => array:sort()'],
  ['New syntax', 'Arrow =>', 'Pipe a value through functions, left to right.',
   'book[last()]/title => upper-case() => tokenize() => string-join('' · '')'],
  ['New syntax', 'Mapping arrow =!>', 'Apply a function to each item of a sequence.',
   'book/@id =!> upper-case() => string-join('', '')'],
  ['New syntax', 'fn { }', 'A short function whose argument is the context item.',
   'filter(book, fn { @pages > 500 })/title ! string()'],
  ['New syntax', 'String templates', 'Backtick strings with expressions in braces.',
   '`{count(book)} books, {sum(book/@pages) => format-number(''#,##0'')} pages`'],
  ['New syntax', 'otherwise', 'A fallback for an empty result.',
   'book[@year > 2030]/title otherwise ''nothing after 2030 yet'''],
  ['New syntax', 'Keyword arguments', 'Name the arguments of a call.',
   'format-integer(value := count(book), picture := ''Ww'')'],
  ['New syntax', 'if { }', 'An if with braces needs no else.',
   'if (count(book) > 5) { ''a long shelf'' }'],
  ['New syntax', 'Number literals', 'Hexadecimal, binary, and _ between digits.',
   '0xFF + 0b11 + 1_000_000'],
  ['Parsing in the stylesheet', 'parse-json', 'JSON text into maps and arrays.',
   'parse-json(ratings)?xslt3'],
  ['Parsing in the stylesheet', 'parse-html', 'HTML text into a tree that the stylesheet can copy.',
   'parse-html(review)//*:p'],
  ['Parsing in the stylesheet', 'element-to-map', 'An XML element as a map, ready for JSON.',
   'element-to-map(book[1]) => serialize(map { ''method'': ''json'', ''indent'': true() })']"/>

 <!-- New functions: one row each. -->
 <xsl:variable name="functions" as="xs:string*" select="
  'index-where(book/@pages, fn { . > 400 })',
  'items-at(book/@id, (6, 1)) ! string()',
  'slice(1 to 10, step := 3)',
  'highest(book, (), fn { xs:integer(@pages) })/@id ! string()',
  'lowest(book, (), fn { xs:integer(@pages) })/@id ! string()',
  'duplicate-values(book/@status ! string())',
  'all-different(book/@id)',
  'partition(book/@id ! string(), fn($a, $b) { count($a) = 2 })',
  'characters(''XSLT'') => insert-separator(''·'') => string-join()',
  'replicate(''ab'', 3) => string-join()',
  'char(''eacute'') || char(0x2192) || char(65)',
  'parse-uri(''https://www.w3.org/TR/'')?host',
  'divide-decimals(10, 3, 2)?quotient',
  'is-NaN(number(''x''))'"/>

 <!-- Show a result: nodes are copied; one atomic value is shown as text; anything else in
      the adaptive serialization (maps, arrays, sequences, quoted strings). -->
 <xsl:function name="f:show">
  <xsl:param name="v" as="item()*"/>
  <xsl:choose>
   <xsl:when test="exists($v) and (every $i in $v satisfies $i instance of node())"><xsl:copy-of select="$v"/></xsl:when>
   <xsl:when test="count($v) = 1 and $v instance of xs:anyAtomicType"><xsl:for-each select="tokenize(string($v), '&#10;')"><p>{.}</p></xsl:for-each></xsl:when>
   <xsl:otherwise>{if (empty($v)) then '()' else string-join($v ! serialize(., map { 'method': 'adaptive' }), ', ')}</xsl:otherwise>
  </xsl:choose>
 </xsl:function>

 <xsl:function name="f:run" as="item()*">
  <xsl:param name="code" as="xs:string"/>
  <xsl:param name="context" as="node()"/>
  <xsl:evaluate xpath="$code" context-item="$context"/>
 </xsl:function>

 <xsl:template name="card">
  <xsl:param name="feature" as="xs:string"/><xsl:param name="what" as="xs:string"/>
  <xsl:param name="code" as="xs:string"/><xsl:param name="out" as="item()*"/>
  <div class="card">
   <p class="head"><span class="chip">{$feature}</span></p>
   <p class="what">{$what}</p>
   <div class="code"><xsl:for-each select="tokenize($code, '&#10;')"><p>{.}</p></xsl:for-each></div>
   <div class="out"><xsl:sequence select="$out"/></div>
  </div>
 </xsl:template>

 <!-- Templates for atomic values, chosen by type. -->
 <xsl:template match="type(xs:integer)" mode="bar">
  <p class="bar"><span class="fill" style="width:{. idiv 5}px"></span> {.}</p>
 </xsl:template>
 <xsl:template match="type(xs:string)" mode="bar">
  <p class="bar"><span class="none">{.}</span></p>
 </xsl:template>

 <xsl:template match="/library">
  <xsl:variable name="lib" select="."/>
  <html lang="en"><head><meta charset="utf-8"/><title>XSLT 4 in a browser</title>
   <style>body{{margin:0;padding:0;font-size:14px;line-height:20px;color:#1d2735;background:#eef1f6}}
.top{{padding:14px 16px 16px 16px;background:#14213d;color:#e5ecf6}}.top a{{color:#ffd166}}
h1{{margin:0;padding-top:6px;font-size:28px;line-height:36px;color:white}}.sub{{margin:0;padding-top:4px;color:#b7c4d8}}
.wrap{{padding:2px 16px 24px 16px}}p{{margin:0}}
h2{{margin:0;padding-top:22px;font-size:13px;line-height:18px;color:#5a6b85;letter-spacing:1px}}
.book{{margin-top:8px;padding:10px 12px;background:white;border:1px solid #d9e0ea}}
.book .t{{font-size:17px;line-height:24px;color:#14213d}}.book .m{{padding-top:2px;font-size:13px;color:#5a6b85}}
.stars{{color:#e0a100;font-size:15px}}
.state{{display:inline-block;padding:0 8px;color:white;font-size:12px;line-height:18px}}
.card{{margin-top:10px;padding:10px 12px 12px 12px;background:white;border:1px solid #d9e0ea}}
.chip{{display:inline-block;padding:1px 8px;background:#e8eefc;color:#2846a8;font-size:14px;line-height:20px}}
.what{{padding-top:6px;color:#3a4658}}
.code{{margin-top:8px;padding:6px 10px;background:#1b2433;color:#cfe3ff;font-size:13px;line-height:19px}}
.out{{margin-top:6px;padding:6px 10px;background:#f2f7ee;color:#1f5130;font-size:14px;line-height:20px;border-left:3px solid #4c9a63}}
.out p{{margin:0;padding:0}}
.bar{{padding-top:3px;font-size:13px;line-height:16px}}.fill{{display:inline-block;height:12px;background:#4c9a63}}.none{{color:#a8432f}}
table{{border-collapse:collapse;background:white}}th{{padding:3px 10px;background:#dfe9da;color:#1f5130;font-size:13px}}td{{padding:3px 10px;border-top:1px solid #dfe9da;font-size:13px}}
.fn{{margin-top:10px;background:white;border:1px solid #d9e0ea}}
.row{{padding:7px 12px;border-top:1px solid #e6ebf2}}.row .c{{font-size:13px;line-height:18px;color:#2846a8}}.row .r{{padding-top:2px;color:#1f5130}}
.about{{margin-top:24px;padding:12px 14px;background:#e3e8f0;color:#3a4658;font-size:13px;line-height:19px}}.about p{{padding-top:4px}}
code{{color:#7a3e12}}</style></head>
  <body>
   <div class="top">
    <p><a href="index.html">Demo index</a></p>
    <h1>XSLT 4 in a browser</h1>
    <p class="sub">Each card is one feature, its code, and the output it gave when this page loaded.</p>
   </div>
   <div class="wrap">
    <h2>THE SHELF</h2>
    <xsl:for-each select="sort(book, (), fn { xs:integer(@year) })">
     <div class="book">
      <p class="t">{title}</p>
      <p class="m"><span class="state" style="background:{$status?(@status)}">{f:label(@status)}</span> {`{@year} · {by} · {@pages} pages`} <span class="stars">{replicate('★', xs:integer($ratings?(@id))) => string-join()}</span></p>
     </div>
    </xsl:for-each>

    <xsl:for-each-group select="$cards" group-adjacent="?1">
     <h2>{upper-case(current-grouping-key())}</h2>
     <xsl:for-each select="current-group()">
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="?2"/><xsl:with-param name="what" select="?3"/>
       <xsl:with-param name="code" select="?4"/>
       <xsl:with-param name="out">
        <xsl:try><xsl:sequence select="f:show(f:run(?4, $lib))"/><xsl:catch>Not in this engine yet: {$err:code}</xsl:catch></xsl:try>
       </xsl:with-param>
      </xsl:call-template>
     </xsl:for-each>
     <xsl:if test="current-grouping-key() = 'Maps and arrays'">
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="'xsl:record-type'"/>
       <xsl:with-param name="what" select="'A named record type, with typed fields and a constructor function.'"/>
       <xsl:with-param name="code" select="'&lt;xsl:record-type name=&quot;f:summary&quot;&gt;&#10;  &lt;xsl:field name=&quot;title&quot; as=&quot;xs:string&quot;/&gt;&#10;  &lt;xsl:field name=&quot;year&quot; as=&quot;xs:integer&quot;/&gt;&#10;&lt;/xsl:record-type&gt;&#10;f:summary(string(book[last()]/title),&#10;  xs:integer(book[last()]/@year))'"/>
       <xsl:with-param name="out" select="f:show(f:summary(string($lib/book[last()]/title), xs:integer($lib/book[last()]/@year)))"/>
      </xsl:call-template>
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="'xsl:array'"/>
       <xsl:with-param name="what" select="'Build an array with an instruction.'"/>
       <xsl:with-param name="code" select="'&lt;xsl:array select=&quot;book ! xs:integer(@year)&quot;/&gt;'"/>
       <xsl:with-param name="out"><xsl:variable name="a" as="array(*)"><xsl:array select="$lib/book ! xs:integer(@year)"/></xsl:variable>{f:show($a)}</xsl:with-param>
      </xsl:call-template>
     </xsl:if>
     <xsl:if test="current-grouping-key() = 'New syntax'">
      <h2>NEW INSTRUCTIONS</h2>
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="'xsl:switch'"/>
       <xsl:with-param name="what" select="'Choose by value: one select, many cases. It sets the labels on the shelf.'"/>
       <xsl:with-param name="code" select="'&lt;xsl:switch select=&quot;string(@status)&quot;&gt;&#10;  &lt;xsl:when test=&quot;''read''&quot;&gt;Read&lt;/xsl:when&gt;&#10;  &lt;xsl:when test=&quot;''reading''&quot;&gt;On the desk&lt;/xsl:when&gt;&#10;  &lt;xsl:otherwise&gt;Wish list&lt;/xsl:otherwise&gt;&#10;&lt;/xsl:switch&gt;'"/>
       <xsl:with-param name="out">{string-join($lib/book ! (@id || ': ' || f:label(@status)), ', ')}</xsl:with-param>
      </xsl:call-template>
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="'match=&quot;type(…)&quot;'"/>
       <xsl:with-param name="what" select="'Template rules for atomic values, chosen by type.'"/>
       <xsl:with-param name="code" select="'&lt;xsl:template match=&quot;type(xs:integer)&quot;&gt; a bar &lt;/xsl:template&gt;&#10;&lt;xsl:template match=&quot;type(xs:string)&quot;&gt; a word &lt;/xsl:template&gt;&#10;&lt;xsl:apply-templates select=&quot;book ! xs:integer(@pages), ''unknown''&quot;/&gt;'"/>
       <xsl:with-param name="out"><xsl:apply-templates select="$lib/book ! xs:integer(@pages), 'unknown'" mode="bar"/></xsl:with-param>
      </xsl:call-template>
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="'xsl:if then else'"/>
       <xsl:with-param name="what" select="'An xsl:if that returns a value either way.'"/>
       <xsl:with-param name="code" select="'&lt;xsl:if test=&quot;sum(book/@pages) > 2000&quot; then=&quot;''a heavy shelf''&quot; else=&quot;''a light shelf''&quot;/&gt;'"/>
       <xsl:with-param name="out"><xsl:if test="sum($lib/book/@pages) > 2000" then="'a heavy shelf'" else="'a light shelf'"/></xsl:with-param>
      </xsl:call-template>
     </xsl:if>
     <xsl:if test="current-grouping-key() = 'Parsing in the stylesheet'">
      <xsl:variable name="csv" select="parse-csv($lib/loans, map { 'header': true() })"/>
      <xsl:call-template name="card">
       <xsl:with-param name="feature" select="'parse-csv'"/>
       <xsl:with-param name="what" select="'CSV text into column names and rows.'"/>
       <xsl:with-param name="code" select="'parse-csv(loans, map { ''header'': true() })'"/>
       <xsl:with-param name="out">
        <table><tr><xsl:for-each select="$csv?columns"><th>{.}</th></xsl:for-each></tr>
         <xsl:for-each select="$csv?rows"><tr><xsl:for-each select="?*"><td>{.}</td></xsl:for-each></tr></xsl:for-each></table>
       </xsl:with-param>
      </xsl:call-template>
     </xsl:if>
    </xsl:for-each-group>

    <h2>NEW FUNCTIONS</h2>
    <div class="fn">
     <xsl:for-each select="$functions">
      <div class="row"><p class="c">{.}</p>
       <div class="r"><xsl:try><xsl:sequence select="f:show(f:run(., $lib))"/><xsl:catch>Not in this engine yet: {$err:code}</xsl:catch></xsl:try></div></div>
     </xsl:for-each>
    </div>

    <div class="about">
     <p>This page is <code>books-xslt4.xml</code> with an XSLT 4.0 stylesheet. Lean's XSLT 4.0 engine ran it, and Lean drew the result.
      The expression cards are run as written, with <code>xsl:evaluate</code>.</p>
     <p>Not in this engine yet: <code>switch</code> and <code>typeswitch</code> expressions in XPath, and some newer functions such as
      <code>map:pairs</code> and <code>scan-left</code> (<a href="https://github.com/danbri/factoidal/issues/1149">issue 1149</a>).</p>
    </div>
   </div>
  </body></html>
 </xsl:template>

 <xsl:function name="f:label" as="xs:string">
  <xsl:param name="s" as="xs:string"/>
  <xsl:switch select="$s">
   <xsl:when test="'read'">Read</xsl:when>
   <xsl:when test="'reading'">On the desk</xsl:when>
   <xsl:otherwise>Wish list</xsl:otherwise>
  </xsl:switch>
 </xsl:function>
</xsl:stylesheet>
