// Deployment host only. XMPP parsing/auth/routing remain in the Lean engine.
import {pathToFileURL} from 'node:url';

export function alphaOptions(env) {
  const domain = new URL(env.PUBLIC_ORIGIN).hostname;
  const cert=env.XMPP_TLS_CERT_PEM || (env.XMPP_TLS_CERT_B64 && Buffer.from(env.XMPP_TLS_CERT_B64,'base64').toString('utf8'));
  const key=env.XMPP_TLS_KEY_PEM || (env.XMPP_TLS_KEY_B64 && Buffer.from(env.XMPP_TLS_KEY_B64,'base64').toString('utf8'));
  if (!cert || !key)
    throw new Error('XMPP alpha requires its runtime TLS certificate and key');
  const accounts = JSON.parse(env.XMPP_ACCOUNTS_JSON || (env.XMPP_ACCOUNTS_B64 && Buffer.from(env.XMPP_ACCOUNTS_B64,'base64').toString('utf8')) || 'null');
  if (!Array.isArray(accounts) || accounts.length < 1 || accounts.length > 8 ||
      new Set(accounts.map(a=>a?.username)).size !== accounts.length ||
      accounts.some(a=>!a || typeof a.username !== 'string' || !/^[a-z0-9_-]{1,32}$/.test(a.username) ||
        typeof a.password !== 'string' || a.password.length < 24 || a.password.length > 256 ||
        Object.keys(a).some(k=>!['username','password'].includes(k))))
    throw new Error('Provide 1–8 unique alpha accounts with 24–256 character passwords');
  return {domain, accounts, cert, key,
    dir:env.XMPP_DIR || '/data/xmpp', pollMs:0, maxBuffered:65536};
}

export async function startAlpha(options, {createXmppServer, host='::', port=5223, onStop=()=>{}}) {
  const running=await createXmppServer(options);
  running.server.maxConnections=4;
  running.server.on('connection',socket=>{
    socket.setTimeout(120000,()=>socket.destroy());
    const lifetime=setTimeout(()=>socket.destroy(),300000);
    lifetime.unref();socket.once('close',()=>clearTimeout(lifetime));
  });
  let timer, stopping;
  const close=()=>stopping ||= (async()=>{clearInterval(timer);await running.close();})();
  try {
    await new Promise((resolve,reject)=>{running.server.once('error',reject);running.server.listen(port,host,resolve);});
    // Coarse alpha watchdog, NOT a proved hard queue bound. Stop only XMPP;
    // LWS/Caddy run separately. Pending messages are volatile and discarded.
    timer=setInterval(()=>{
      let count=0,bytes=0;
      for(const messages of running.pending().values()) for(const message of messages){count++;bytes+=Buffer.byteLength(message);}
      if(count>128 || bytes>262144) void close().then(()=>onStop('XMPP alpha stopped: pending queue budget exceeded'));
    },250);
    timer.unref();
    return {...running,close,port:running.server.address().port};
  } catch(error){await close();throw error;}
}

if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href){
  const {createXmppServer}=await import('@factoidal/core/xmpp/server');
  const running=await startAlpha(alphaOptions(process.env),{createXmppServer,onStop:reason=>{console.error(reason);process.exitCode=1;}});
  console.log('XMPP alpha: private direct-TLS port 5223, fixed accounts; no public port configured');
  for(const signal of ['SIGINT','SIGTERM']) process.once(signal,async()=>{await running.close();process.exit(0);});
}
