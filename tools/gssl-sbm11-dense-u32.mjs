// Optional dense u32 remapping of a bounded SBM11 u64 *snapshot*.
// This is NOT a truncating cast or a new RDF identity semantics. The
// dictionary is query-scope only; an active graph/snapshot token is mandatory
// before production reuse. No query matching is performed in this module.
import {parseId,packTriples64} from "./gssl-sbm11-webgpu.mjs";

export function denseRemap64(rows,constants,{maxTerms=0xffffffff-1}={}){
  if(!Number.isSafeInteger(maxTerms)||maxTerms<1||maxTerms>0xffffffff-1)
    throw new RangeError("Invalid dense u32 dictionary capacity.");
  const {triples} = packTriples64(rows);
  const dictionary=[null]; // code 0 remains unbound, never an RDF term.
  const codes=new Map();
  const codeOf = term=>{
    const u64=parseId(term);
    const key=u64.toString();
    let id=codes.get(key);
    if(id===undefined){
      if(dictionary.length>maxTerms)
        throw new RangeError("Dense u32 dictionary capacity exceeded.");
      id=dictionary.length;
      dictionary.push(u64);
      codes.set(key,id);
    }
    return id;
  };
  const input=triples.map(t=>t.map(codeOf));
  const queryConstants={
    knows:codeOf(constants.knows),
    works:codeOf(constants.works),
    atlas:codeOf(constants.atlas),
  };
  const decode = value=>{
    if(!Number.isSafeInteger(value)||value<1||value>=dictionary.length)
      throw new RangeError("Unrecognized or unbound dense u32 code.");
    return dictionary[value];
  };
  return {
    triples:input,queryConstants,
    dictionarySize:dictionary.length-1,
    entries:dictionary.slice(1).map((term,i)=>({code:i+1,global:term.toString()})),
    decode,codeOf,
  };
}
export function decodeDensePairs(pairs,dense){
  if(!Array.isArray(pairs))throw new TypeError("Expected GPU result pairs.");
  return pairs.map(pair=>{
    if(!Array.isArray(pair)||pair.length!==2)throw new TypeError("Invalid GPU pair.");
    return [dense.decode(pair[0]),dense.decode(pair[1])];
  });
}
