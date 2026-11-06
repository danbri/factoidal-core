// Independent verification of the frozen wire fixtures, not their metadata.
import test,{after} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {FIXTURES} from '../../docs/web/hub/xml-signature/fixtures.mjs';
const dir=mkdtempSync(join(tmpdir(),'signature-oracle-'));after(()=>rmSync(dir,{recursive:true,force:true}));
function verify(xml,embedded=false){
  const path=join(dir,'document.xml');writeFileSync(path,xml);
  const r=spawnSync('java',[fileURLToPath(new URL('./xml-signature-fixtures/MakeFixtures.java',import.meta.url)),
    FIXTURES.publicKey.n,FIXTURES.publicKey.e,path,embedded?'xslt-oracle-only':'strict'],{encoding:'utf8',timeout:30000});
  assert.ifError(r.error);assert.equal(r.status,0,r.stderr);assert.equal(r.stderr,'');return r.stdout.trim();
}
test('independent JDK verifies the actual frozen standard signatures and rejects covered tamper',()=>{
  assert.equal(verify(FIXTURES.signedOriginal),'true');assert.equal(verify(FIXTURES.signedProjected),'true');
  assert.equal(verify(FIXTURES.signedOriginal.replace('1200','9000')),'false');
});
test('independent pedagogic XSLT signature validates ONLY with its explicitly relaxed oracle setting',()=>{
  assert.equal(verify(FIXTURES.embeddedXslt,true),'true');
  assert.throws(()=>verify(FIXTURES.embeddedXslt),/forbidden when secure validation/i);
  // Not a recommendation to enable this setting in any production verifier.
});
