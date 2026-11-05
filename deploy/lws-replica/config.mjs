export function replicaOptions(env, jwks) {
  const origin = new URL(env.PUBLIC_ORIGIN);
  if (origin.protocol !== 'https:' || origin.username || origin.password || origin.pathname !== '/' || origin.search || origin.hash)
    throw new Error('PUBLIC_ORIGIN must be an HTTPS origin, without path or credentials');
  const subject = env.WRITER_SUBJECT;
  if (!subject || !/^[a-z][a-z0-9+.-]*:/i.test(subject) || /[\s<>"{}|^`\\]/u.test(subject))
    throw new Error('WRITER_SUBJECT must be a safe absolute IRI');
  if (!jwks || !Array.isArray(jwks.keys) || jwks.keys.length !== 1)
    throw new Error('Exactly one laptop public key is required');
  const k = jwks.keys[0];
  const allowed = new Set(['kty','crv','x','kid','alg','use','key_ops']);
  if (Object.keys(k).some(x => !allowed.has(x)) || k.kty !== 'OKP' || k.crv !== 'Ed25519' ||
      typeof k.x !== 'string' || !/^[A-Za-z0-9_-]{43}$/.test(k.x) || !k.kid ||
      k.alg !== 'EdDSA' || k.use !== 'sig')
    throw new Error('Expected a public Ed25519 signing JWK; private/symmetric keys are forbidden');
  const baseIri = `${origin.origin}/lws/`;
  const issuer = `${origin.origin}/laptop-issuer`;
  const rootAcl = `@prefix acl: <http://www.w3.org/ns/auth/acl#> .
@prefix foaf: <http://xmlns.com/foaf/0.1/> .
<${baseIri}.acl#public> a acl:Authorization; acl:agentClass foaf:Agent;
 acl:accessTo <${baseIri}>; acl:default <${baseIri}>; acl:mode acl:Read.
<${baseIri}.acl#writer> a acl:Authorization; acl:agent <${subject}>;
 acl:accessTo <${baseIri}>; acl:default <${baseIri}>; acl:mode acl:Read, acl:Write.
<${baseIri}.acl#controller> a acl:Authorization; acl:agent <urn:factoidal:offline-controller>;
 acl:accessTo <${baseIri}>; acl:default <${baseIri}>; acl:mode acl:Control.
`;
  return { host:'127.0.0.1', port:3000, dir:env.LWS_DIR || '/data/lws',
    baseIri, rootAcl, realClock:true, auth:{audience:baseIri, issuers:[{issuer,jwks}]},
    notifications:false, accessGrants:false, moves:false, linksetPut:false,
    typeIndex:false, searchResults:false, cors:[origin.origin] };
}
