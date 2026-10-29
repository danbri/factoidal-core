<p:declare-step xmlns:p="http://www.w3.org/ns/xproc"
  version="3.1" name="dynamically-executed-pipeline">
  <p:input port="source" primary="true">
    <p:inline><doc/></p:inline>
  </p:input>
  <p:output port="result" primary="true"/>
  <p:option name="parameters" as="map(*)"/>
  <p:cast-content-type content-type="application/xml">
    <p:with-input select="$parameters"/>
  </p:cast-content-type>
</p:declare-step>
