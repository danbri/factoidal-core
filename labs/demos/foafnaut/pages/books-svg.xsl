<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="3.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns="http://www.w3.org/2000/svg" expand-text="yes">
 <xsl:output method="xml"/>
 <xsl:template match="/library">
  <html xmlns="http://www.w3.org/1999/xhtml" lang="en"><head><title>{@name} as a chart</title>
   <style>body{{margin:16px;font-size:14px;line-height:20px;color:#203040;background:white}}h1{{margin:0;font-size:21px;line-height:28px;color:#184078}}p{{margin:0;padding-top:6px}}svg{{display:block}}</style></head>
  <body><main>
   <p><a href="index.html">Demo index</a></p>
   <h1>Pages in each book</h1>
   <p>This page is XML. Lean ran an XSLT 3.0 stylesheet that made these SVG bars.</p>
   <svg width="600" height="{count(book)*40}" viewBox="0 0 600 {count(book)*40}">
    <xsl:for-each select="book">
     <rect x="0" y="{(position()-1)*40+6}" width="{number(pages) div 2}" height="28" fill="#184078"/>
    </xsl:for-each>
   </svg>
  </main></body></html>
 </xsl:template>
</xsl:stylesheet>
