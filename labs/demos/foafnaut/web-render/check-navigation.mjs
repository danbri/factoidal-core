#!/usr/bin/env node
import assert from 'node:assert/strict';
import {once} from 'node:events';
import {makeNavigationFixture} from './navigation-fixture.mjs';
import {makeServer} from './server.mjs';
import {fetchResource} from './resource-client.mjs';
import {fetchResourceBytes} from './resource-broker.mjs';
import {NavigationController,navigationURL} from './navigation.mjs';
const fixture=makeNavigationFixture(),broker=makeServer();
fixture.server.listen(0,'127.0.0.1');broker.listen(0,'127.0.0.1');await Promise.all([once(fixture.server,'listening'),once(broker,'listening')]);
const origin=`http://127.0.0.1:${fixture.server.address().port}`,endpoint=`http://127.0.0.1:${broker.address().port}/resource`,rendered=[],states=[];
const navigation=new NavigationController({load:(url,options)=>fetchResource(url,{...options,endpoint}),render:async(resource,context)=>{assert(context.isCurrent());rendered.push(resource.text());},onState:state=>states.push(state)});
const checks=[];
try{
 assert(await navigation.go(origin+'/one'));assert.equal(rendered.at(-1),fixture.pages['/one']);
 assert(await navigation.go('two?from=one'));assert.equal(navigation.snapshot().url,origin+'/two?from=one');assert.equal(rendered.at(-1),fixture.pages['/two']);
 assert(await navigation.back());assert.equal(navigation.snapshot().url,origin+'/one');assert(await navigation.forward());assert.equal(navigation.snapshot().url,origin+'/two?from=one');
 const count=fixture.requests.length;assert(await navigation.reload());assert.equal(fixture.requests.length,count+1);assert.equal(navigation.entries.length,2);checks.push('unchanged HTTP page bytes, relative links, back, forward and refetch on reload');
 assert(await navigation.go(origin+'/redirect#anchor'));assert.equal(navigation.snapshot().url,origin+'/two?redirected=1#anchor');checks.push('redirect final URL and fragment identity');
 const before=navigation.snapshot();assert.equal(await navigation.go(origin+'/missing'),false);assert.equal(navigation.snapshot().url,before.url);assert.equal(navigation.entries.length,before.entries.length);assert.match(states.at(-1).error,/404/);checks.push('failed navigation does not commit history');
 const slow=navigation.go(origin+'/slow');await navigation.go(origin+'/one');assert.equal(await slow,false);assert.equal(navigation.snapshot().url,origin+'/one');assert(!rendered.includes(fixture.pages['/slow']));
 const stop=navigation.go(origin+'/slow');navigation.cancel();assert.equal(await stop,false);assert.equal(navigation.snapshot().loading,false);checks.push('abort and latest request prevent stale page commits');
 await assert.rejects(fetchResourceBytes(origin+'/loop'),/Too many/);await assert.rejects(fetchResourceBytes(origin+'/large'),/byte limit/);
 const invalid=await fetchResource(origin+'/bad-utf8',{endpoint});assert.throws(()=>invalid.text(),/UTF-8/);
 assert.throws(()=>navigationURL('javascript:alert(1)'),/scheme/);assert.throws(()=>navigationURL('https://name:secret@example.org/'),/credentials/);
 const foreign=await fetch(endpoint+'?url='+encodeURIComponent(origin+'/one'),{headers:{Origin:'https://foreign.invalid'}});assert.equal(foreign.status,403);checks.push('redirect, size, UTF-8, scheme, credentials and broker origin failures');
 console.log(JSON.stringify({status:'PASS',checks,fixtureRequests:fixture.requests.length},null,2));
}finally{fixture.server.closeAllConnections();broker.closeAllConnections();await Promise.all([new Promise(resolve=>fixture.server.close(resolve)),new Promise(resolve=>broker.close(resolve))]);}
