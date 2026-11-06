/** XML Signature coverage lab. XML/XSLT/canonicalization/verification decisions
 * run in the Lean engine. JS marshals JSON and displays the returned coverage decision.
 * Frozen demo signatures are copied, never recomputed or claimed as new signing.
 */
import {FIXTURES,INITIAL_SOURCE,INITIAL_STYLESHEET,PRESETS} from './fixtures.mjs';
export {INITIAL_SOURCE,INITIAL_STYLESHEET,PRESETS};

const proofScope = Object.freeze({
  theorem:'L4Factoidal.XML.DSig.verifyEnveloped_ok',
  coverageTheorem:'L4Wasm.Ops.XmlSignature.coverage_iff',
  scope:'Successful strict verification implies the document-root reference digest matched and the supplied RSA verifier accepted canonical SignedInfo.',
  assumptions:['HACL* RSA public operation and FFI','caller-pinned public key','compiled engine and JS/WASM transport'],
  notProved:['user intent or consent','certificate trust or identity','XSLT preservation of business meaning','whole compositor/browser execution'],
  pipelineProved:false
});
async function call(engine,op,args){
  let result;
  try { result=await engine.call(op,args); }
  catch(error){
    const envelope=error?.envelope;
    throw new Error(`${op}: ${envelope?.error || error?.message || 'engine call failed'}`,{cause:error});
  }
  if(typeof result==='string') result=JSON.parse(result);
  if(!result || result.ok!==true) throw new Error(`${op}: ${result?.error || 'invalid engine response'}`);
  return result;
}
export async function runSignatureDemo({engine,source=INITIAL_SOURCE,stylesheet=INITIAL_STYLESHEET,mode='original',tamper=false}={}){
  if(!engine || typeof engine.call!=='function') throw new TypeError('A fresh full Lean engine with call(op,args) is required; old engines cannot verify this demo.');
  if(typeof source!=='string'||typeof stylesheet!=='string') throw new TypeError('source and stylesheet must be strings');
  if(!PRESETS.some(p=>p.id===mode)) throw new TypeError('unknown signature demonstration mode');
  if(typeof tamper!=='boolean') throw new TypeError('tamper must be boolean');
  const stages=[];
  stages.push({id:'source',title:'Intended approval XML',input:'editable XML',output:source,evidence:{kind:'input',proved:false}});
  const transformed=await call(engine,'xslt4Transform',[stylesheet,source]);
  if(transformed.method!=='xml') throw new Error('This lab requires an XML XSLT result, not HTML/text serialization.');
  const transformedXml=transformed.output;
  stages.push({id:'transform',title:'Actual Lean XSLT preprocessing',input:source,output:transformedXml,
    evidence:{kind:'runtime',operation:'xslt4Transform',proved:false,note:'Preprocessing before signature verification; not a ds:Transform.'}});
  // The tamper option itself is an additional real XSLT step, not JS XML editing.
  let candidate=mode==='preprocessed'?transformedXml:source;
  if(tamper){
    const changed=await call(engine,'xslt4Transform',[TAMPER_STYLESHEET,candidate]);candidate=changed.output;
    stages.push({id:'tamper',title:'Change payee after frozen signing',input:'actual XSLT replacement',output:candidate,
      evidence:{kind:'runtime',operation:'xslt4Transform',proved:false}});
  }
  const signatureDocument=mode==='preprocessed'?FIXTURES.signedProjected:mode==='embedded-xslt'?FIXTURES.embeddedXslt:FIXTURES.signedOriginal;
  const verification=await call(engine,'xmlSignatureVerify',[JSON.stringify({document:candidate,signatureDocument,expectedDocument:source,publicKey:FIXTURES.publicKey})]);
  stages.push({id:'verify',title:'Copy frozen signature; verify actual candidate',input:candidate,output:verification.document,
    evidence:{kind:'runtime',operation:'xmlSignatureVerify',valid:verification.valid,proofScope,
      note:'The private key is absent. Edited content is checked against the unchanged fixture signature.'}});
  if(typeof verification.coversExpected!=='boolean') throw new Error('xmlSignatureVerify: missing Lean coverage decision');
  const matchesOriginal=verification.coversExpected;
  const warning=verification.valid!==true
    ? `Verification refused: ${verification.verificationError || 'strict profile refused input'}`
    : matchesOriginal
      ? 'The signature covers the canonical original approval under this fixed profile. This is not a certificate or user-consent claim.'
      : 'VALID SIGNATURE, DIFFERENT COVERAGE: only the transformed document is signed. The original amount/account are not authenticated by it.';
  const intent={matchesOriginal,warning,comparison:'Lean coverage_iff: verified and canonical reference equals expected canonical document; not business intent'};
  stages.push({id:'coverage',title:'Coverage versus intended original',input:verification.canonicalReference || '',output:warning,
    evidence:{kind:'lean-coverage-decision',proved:false,matchesOriginal,comparison:intent.comparison}});
  return {stages,mode,originalXml:source,transformedXml,signedXml:verification.document,verification,intent,evidence:proofScope,
    fixtureOracle:FIXTURES.oracle,fixtureSigning:'Frozen JDK RSA-2048 signatures; no browser private key, no signing service.'};
}
const TAMPER_STYLESHEET='<xsl:stylesheet version="3.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:output method="xml" omit-xml-declaration="yes"/><xsl:mode on-no-match="shallow-copy"/><xsl:template match="payee"><payee>Changed recipient</payee></xsl:template></xsl:stylesheet>';
