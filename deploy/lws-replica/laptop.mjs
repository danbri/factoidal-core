// Operator tool. Private keys are generated/stored ONLY on the laptop.
import {generateKeyPairSync,createPrivateKey,sign} from 'node:crypto';
import {mkdir,readFile,writeFile} from 'node:fs/promises';
import {join} from 'node:path';
const [command,dir,origin,subject]=process.argv.slice(2);
if(command==='init' && dir){
  await mkdir(dir,{recursive:true,mode:0o700});
  const {privateKey,publicKey}=generateKeyPairSync('ed25519');
  // Exclusive create prevents accidental replacement of a live writer key.
  await writeFile(join(dir,'writer.private.pem'),privateKey.export({type:'pkcs8',format:'pem'}),{mode:0o600,flag:'wx'});
  const key={...publicKey.export({format:'jwk'}),kid:'laptop-1',alg:'EdDSA',use:'sig'};
  await writeFile(join(dir,'writer.jwks.json'),JSON.stringify({keys:[key]},null,2)+'\n',{mode:0o644,flag:'wx'});
  console.log('Created laptop key and public JWKS. Copy ONLY writer.jwks.json to the server.');
}else if(command==='token' && dir && origin && subject){
  const u=new URL(origin);if(u.protocol!=='https:'||u.origin!==origin)throw new Error('Origin must be https://hostname without trailing slash');
  const key=createPrivateKey(await readFile(join(dir,'writer.private.pem')));
  const now=Math.floor(Date.now()/1000);
  const enc=x=>Buffer.from(JSON.stringify(x)).toString('base64url');
  const payload=enc({alg:'EdDSA',typ:'at+jwt',kid:'laptop-1'})+'.'+enc({iss:origin+'/laptop-issuer',sub:subject,aud:origin+'/lws/',iat:now,nbf:now-5,exp:now+300});
  console.log(payload+'.'+sign(null,Buffer.from(payload),key).toString('base64url'));
}else throw new Error('Usage: node laptop.mjs init PRIVATE_DIR | token PRIVATE_DIR HTTPS_ORIGIN WRITER_SUBJECT');
