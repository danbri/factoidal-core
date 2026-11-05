<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="4.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" expand-text="yes">
 <xsl:output method="html"/>
 <xsl:template match="/library">
  <html lang="en"><head><title>{@name} (XSLT 4.0)</title>
   <style>body{{margin:16px;font-size:14px;line-height:20px;color:#203040;background:white}}h1{{margin:0;font-size:21px;line-height:28px;color:#184078}}h2{{margin:0;padding-top:10px;font-size:16px;line-height:22px}}p{{margin:0;padding-top:6px}}</style></head>
  <body><main>
   <p><a href="index.html">Demo index</a></p>
   <h1>{@name}</h1>
   <p>This page is XML. Lean ran an XSLT 4.0 stylesheet, with text value templates and grouping, then rendered the HTML result.</p>
   <xsl:for-each-group select="book" group-by="substring(@year,1,2) || '00s'">
    <xsl:sort select="current-grouping-key()"/>
    <h2>{current-grouping-key()}: {count(current-group())} books</h2>
    <xsl:for-each select="current-group()">
     <xsl:sort select="xs:integer(@year)" xmlns:xs="http://www.w3.org/2001/XMLSchema"/>
     <p>{@year}: {title}, by {by}</p>
    </xsl:for-each>
   </xsl:for-each-group>
  </main></body></html>
 </xsl:template>
</xsl:stylesheet>
