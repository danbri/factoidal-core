// Run on the laptop, with a destination OUTSIDE the Docker build context.
import {mkdir,readFile,writeFile,chmod} from 'node:fs/promises';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {randomBytes} from 'node:crypto';
const [directory,hostname]=process.argv.slice(2);
if(!directory || !hostname || !/^[a-z0-9][a-z0-9.-]+[a-z0-9]$/i.test(hostname))
  throw new Error('Usage: node provision-xmpp.mjs NEW_PRIVATE_DIRECTORY APP.fly.dev');
const dir=resolve(directory),context=fileURLToPath(new URL('.',import.meta.url));
if((dir+'/').startsWith(context))throw new Error('Keep secrets outside the build context');
process.umask(0o077);
await mkdir(dir,{mode:0o700}); // Exclusive directory creation: never replace existing credentials.
execFileSync('openssl',['req','-x509','-newkey','rsa:2048','-nodes','-days','30',
  '-subj',`/CN=${hostname}`,'-addext',`subjectAltName=DNS:${hostname}`,
  '-keyout',join(dir,'tls.key'),'-out',join(dir,'tls.crt')],{stdio:'ignore'});
await chmod(join(dir,'tls.key'),0o600);
const accounts=['laptop','replica'].map(username=>({username,password:randomBytes(32).toString('base64url')}));
await writeFile(join(dir,'accounts.json'),JSON.stringify(accounts,null,2)+'\n',{mode:0o600,flag:'wx'});
const cert=(await readFile(join(dir,'tls.crt'))).toString('base64');
const key=(await readFile(join(dir,'tls.key'))).toString('base64');
// Base64 values are single-line and do not depend on dotenv quote handling.
const secrets='XMPP_ENABLED=true\nXMPP_TLS_CERT_B64='+cert+'\nXMPP_TLS_KEY_B64='+key+
  '\nXMPP_ACCOUNTS_B64='+Buffer.from(JSON.stringify(accounts)).toString('base64')+'\n';
await writeFile(join(dir,'fly-secrets.env'),secrets,{mode:0o600,flag:'wx'});
console.log('Created two alpha accounts, 30-day test TLS certificate and Fly import file. Secrets were not printed.');
