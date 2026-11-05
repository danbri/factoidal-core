import {readFile} from 'node:fs/promises';
import {listen} from '@factoidal/core/lws';
import {replicaOptions} from './config.mjs';
import {startReadonlyDav} from './webdav-readonly.mjs';
async function writerKeys() {
  if (process.env.WRITER_JWKS_JSON) return JSON.parse(process.env.WRITER_JWKS_JSON);
  try {
    return JSON.parse(await readFile(process.env.WRITER_JWKS_FILE || '/run/config/writer.jwks.json','utf8'));
  } catch (error) {
    if (error.code === 'ENOENT') throw new Error('Missing laptop PUBLIC key: provision with laptop.mjs init on the laptop, then set Fly WRITER_JWKS_JSON to writer.jwks.json. XMPP credentials do not provide the LWS writer key. Never upload writer.private.pem.');
    throw error;
  }
}
const jwks = await writerKeys();
const options=replicaOptions(process.env,jwks);
const running = await listen(options);
console.log('LWS replica receiver ready on loopback:3000; authorization enabled');
let dav;
if(process.env.WEBDAV_ENABLED!=='false'){
  const {listen:davListen}=await import('@factoidal/core/webdav');
  dav=await startReadonlyDav({baseIri:options.baseIri,engine:(await running.storage()).engine,listen:davListen});
  console.log('Public read-only WebDAV ready at /dav/ via the LWS HTTP API');
}
for (const signal of ['SIGINT','SIGTERM']) process.once(signal,async()=>{
  await dav?.close();
  await running.close(); process.exit(0);
});
