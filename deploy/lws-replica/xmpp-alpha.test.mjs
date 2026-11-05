import test from 'node:test';
import assert from 'node:assert/strict';
import {alphaOptions,startAlpha} from './xmpp-alpha.mjs';
import {mkdtemp,readFile,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {execFileSync} from 'node:child_process';
import tls from 'node:tls';
import {once} from 'node:events';
const env={PUBLIC_ORIGIN:'https://alpha.example',XMPP_TLS_CERT_PEM:'cert',XMPP_TLS_KEY_PEM:'key',
  XMPP_ACCOUNTS_JSON:JSON.stringify([{username:'alice',password:'a'.repeat(32)}])};
test('alpha config requires TLS and bounded explicit accounts',()=>{
  assert.equal(alphaOptions(env).domain,'alpha.example');
  assert.throws(()=>alphaOptions({...env,XMPP_TLS_KEY_PEM:''}));
  assert.throws(()=>alphaOptions({...env,XMPP_ACCOUNTS_JSON:'[]'}));
  assert.throws(()=>alphaOptions({...env,XMPP_ACCOUNTS_JSON:JSON.stringify([{username:'alice',password:'short'}])}));
});
test('real Lean XMPP over trusted direct TLS: auth, bind, routing and bad-password refusal',async()=>{
  const dir=await mkdtemp(join(tmpdir(),'xmpp-alpha-'));let running;const clients=[];
  try{
    execFileSync('openssl',['req','-x509','-newkey','rsa:2048','-nodes','-days','1','-subj','/CN=alpha.example',
      '-addext','subjectAltName=DNS:alpha.example','-keyout',join(dir,'key.pem'),'-out',join(dir,'cert.pem')],{stdio:'ignore'});
    const cert=await readFile(join(dir,'cert.pem'),'utf8'),key=await readFile(join(dir,'key.pem'),'utf8');
    const core=await import('@factoidal/core');
    const {createXmppServer}=await import('../../npm/factoidal/xmpp/server.mjs');
    running=await startAlpha({...alphaOptions({...env,XMPP_TLS_CERT_PEM:cert,XMPP_TLS_KEY_PEM:key}),dir,
      engine:await core.loadEngine()},{createXmppServer,host:'127.0.0.1',port:0});
    const connect=async()=>{
      const socket=tls.connect({host:'127.0.0.1',port:running.port,servername:'alpha.example',ca:cert});clients.push(socket);
      let buffer='';socket.on('data',chunk=>buffer+=chunk);
      await once(socket,'secureConnect');assert.equal(socket.authorized,true);
      return {socket,reset:()=>buffer='',wait:async needle=>{
        for(let i=0;i<100;i++){if(buffer.includes(needle))return buffer;await new Promise(r=>setTimeout(r,20));}
        throw new Error('No expected XMPP response: '+needle);
      }};
    };
    const stream="<stream:stream to='alpha.example' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>";
    const auth=pw=>"<auth xmlns='urn:ietf:params:xml:ns:xmpp-sasl' mechanism='PLAIN'>"+Buffer.from('\0alice\0'+pw).toString('base64')+'</auth>';
    const good=await connect();good.socket.write(stream);await good.wait('</stream:features>');good.reset();
    good.socket.write(auth('a'.repeat(32)));await good.wait('<success');good.reset();
    good.socket.write(stream);await good.wait('</stream:features>');good.reset();
    good.socket.write("<iq type='set' id='bind'><bind xmlns='urn:ietf:params:xml:ns:xmpp-bind'><resource>test</resource></bind></iq>");
    assert.match(await good.wait('</iq>'),/alice@alpha.example\/test/);
    const second=await connect();second.socket.write(stream);await second.wait('</stream:features>');second.reset();
    second.socket.write(auth('a'.repeat(32)));await second.wait('<success');second.reset();
    second.socket.write(stream);await second.wait('</stream:features>');second.reset();
    second.socket.write("<iq type='set' id='bind2'><bind xmlns='urn:ietf:params:xml:ns:xmpp-bind'><resource>other</resource></bind></iq>");
    await second.wait('</iq>');second.reset();
    good.socket.write("<message to='alice@alpha.example/other' type='chat'><body>alpha-route</body></message>");
    assert.match(await second.wait('</message>'),/alpha-route/);
    const bad=await connect();bad.socket.write(stream);await bad.wait('</stream:features>');bad.reset();
    bad.socket.write(auth('wrong'));await bad.wait('<failure');
  }finally{for(const c of clients)c.destroy();await running?.close();await rm(dir,{recursive:true,force:true});}
});
