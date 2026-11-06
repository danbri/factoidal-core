// Deliberately limited WGSL editor helper; no parser/evaluator or renderer semantics.
// Only decimal floating literals outside comments, indices and array types.
export function scalarLiterals(source){
 let mask='',depth=0,line=false;
 for(let i=0;i<source.length;i++){
  if(line){if(source[i]==='\n'){line=false;mask+='\n';}else mask+=' ';continue;}
  if(depth){if(source.slice(i,i+2)==='/*'){depth++;mask+='  ';i++;}else if(source.slice(i,i+2)==='*/'){depth--;mask+='  ';i++;}else mask+=source[i]==='\n'?'\n':' ';continue;}
  if(source.slice(i,i+2)==='//'){line=true;mask+='  ';i++;}else if(source.slice(i,i+2)==='/*'){depth=1;mask+='  ';i++;}else mask+=source[i];
 }
 const skip=[];let square=0,start=0;
 for(let i=0;i<mask.length;i++){if(mask[i]==='['){if(square++===0)start=i;}else if(mask[i]===']'&&square&&--square===0)skip.push([start,i+1]);}
 for(const m of mask.matchAll(/\barray\s*</g)){let n=1,end=m.index+m[0].length;for(;end<mask.length&&n;end++){if(mask[end]==='<')n++;else if(mask[end]==='>')n--;}skip.push([m.index,end]);}
 const result=[];
 for(const m of mask.matchAll(/\d+\.\d+(?:[eE][+-]?\d+)?[fh]?/g)){
  const from=m.index,to=from+m[0].length;
  if(/[\w.\-]/.test(mask[from-1]??'')||/[\w.]/.test(mask[to]??'')||skip.some(([a,b])=>from>=a&&from<b))continue;
  const value=Number(m[0].replace(/[fh]$/,''));if(!Number.isFinite(value)||value<0||value>10000)continue;
  const line=source.slice(0,from).split('\n').length,context=source.slice(source.lastIndexOf('\n',from)+1,source.indexOf('\n',from)<0?source.length:source.indexOf('\n',from));
  result.push({from,to,value,suffix:/[fh]$/.exec(m[0])?.[0]??'',line,context:context.slice(0,140)});
 }
 return result;
}
export function replaceScalar(source,token,value){
 if(!Number.isFinite(value)||value<0||value>10000)throw Error('Scalar must be finite and within 0…10000.');
 if(!scalarLiterals(source).some(t=>t.from===token.from&&t.to===token.to))throw Error('Scalar position is stale. Select it again.');
 let text=String(Number(value.toPrecision(7)));if(!/[.eE]/.test(text))text+='.0';
 return source.slice(0,token.from)+text+token.suffix+source.slice(token.to);
}
