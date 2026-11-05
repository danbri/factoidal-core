<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
 <xsl:output method="html"/>
 <xsl:template match="/library">
  <html lang="en"><head><title><xsl:value-of select="@name"/> (XSLT 1.0)</title>
   <style>body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:white}h1{margin:0;font-size:21px;line-height:28px;color:#184078}p{margin:0;padding-top:6px}</style></head>
  <body><main>
   <p><a href="index.html">Demo index</a></p>
   <h1><xsl:value-of select="@name"/></h1>
   <p>This page is XML. Lean ran an XSLT 1.0 stylesheet, then rendered the HTML result.</p>
   <xsl:apply-templates select="book"><xsl:sort select="@year" data-type="number"/></xsl:apply-templates>
   <p><xsl:value-of select="count(book)"/> books, <xsl:value-of select="sum(book/pages)"/> pages.</p>
  </main></body></html>
 </xsl:template>
 <xsl:template match="book">
  <p><xsl:value-of select="@year"/>: <xsl:value-of select="title"/>, by <xsl:value-of select="by"/></p>
 </xsl:template>
</xsl:stylesheet>
