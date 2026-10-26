// One port (8080) in front of the two Factoidal servers of this container.
// It forwards each request unchanged, bytes and headers, to one of them by
// path, and makes no other decision: every status, header and body comes from
// lws-serve or authz-serve, whose decisions are made in Lean.
//
// The router of Touchstone's targetservers strips /targets/<name> from the
// path ("strip" mode), and sends the RFC 8414 metadata URL of the issuer to
// /.well-known/lws-configuration. authz-serve answers at paths that carry its
// issuer's path (formal/lean4/L4Factoidal/Authz/Server.lean, issuerPath), so
// this front puts AS_PREFIX back on the four authorization server paths, and
// on the protected resource metadata path (below).
// Everything else goes to lws-serve. A storage resource cannot be named
// /token or /jwks at the storage root.
import http from 'node:http'

const prefix = process.env.AS_PREFIX ?? ''
const LWS = 8081
const AS = 8082

function route (url) {
  const q = url.indexOf('?')
  const path = q < 0 ? url : url.slice(0, q)
  const query = q < 0 ? '' : url.slice(q)
  if (path === '/.well-known/lws-configuration' || path === '/.well-known/oauth-authorization-server') {
    return [AS, path + prefix + query]
  }
  if (path === '/token' || path === '/jwks') return [AS, prefix + path + query]
  // RFC 9728 puts the well-known segment before the resource's whole path. The
  // router sends <origin>/.well-known/oauth-protected-resource/targets/<name>/<rest>
  // here as /.well-known/oauth-protected-resource/<rest>; lws-serve answers the
  // form with the prefix, which its own 401 names.
  const prm = '/.well-known/oauth-protected-resource'
  if (prefix && (path === prm || path.startsWith(prm + '/')) && !path.startsWith(prm + prefix + '/')) {
    return [LWS, prm + prefix + (path.slice(prm.length) || '/') + query]
  }
  return [LWS, url]
}

http.createServer((req, res) => {
  const [port, path] = route(req.url)
  const up = http.request({ host: '127.0.0.1', port, method: req.method, path, headers: req.headers }, (r) => {
    res.writeHead(r.statusCode, r.rawHeaders)
    r.pipe(res)
  })
  up.on('error', (e) => {
    if (!res.headersSent) res.writeHead(502, { 'content-type': 'text/plain' })
    res.end(`upstream ${port}: ${e.message}\n`)
  })
  req.pipe(up)
}).listen(8080, '0.0.0.0')
