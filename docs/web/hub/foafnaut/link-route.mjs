// Where a link goes (WebRoute.lean, owner 2026-11-08). Lean decides: the op shellRoute takes
// the href, the address of the page it is on and the site, and answers the final action:
//   {route:'page',name,url}      a page of the browser itself (foafnaut:bookmarks, settings, ...)
//   {route:'graph',url}          the graph app, at foafnaut:graph
//   {route:'navigate',url}       load url in the tab
//   {route:'system',url}         hand url to the system (the host browser, mail, phone)
//   {route:'command',name,argument}  a browser command (theme, zoom, back, ...)
//   {route:'refuse',url,reason}  do nothing, and say why
// The hosts do what it says and test no URL themselves. An engine from before the op
// (issue 1274) answers "unknown document operation"; for it, fallbackRoute gives the same
// answers in JavaScript. link_route_test.ts runs a few thousand links through both and
// they must agree on every one, so this file follows WebRoute.lean rule for rule.

const externalHosts=['github.com','www.github.com','duckduckgo.com'];
const systemSchemes=['mailto','tel','sms'];
const builtinPages=new Map([['bookmarks',false],['history',false],['settings',false],['wasm',true],['sparql',true],['console',true]]);
const commands=['back','forward','reload','new','close','home','source','theme','zoom','bookmark','unbookmark','pod','sync','sparql-step','classic','encoding','liberal'];
const special=scheme=>scheme==='http'||scheme==='https'||scheme==='file';
const noHost='a relative link needs a web page or a local file around it';

/** An href as a browser reads it: no space or control at either end, no tab or line break inside. */
export function clean(href){
  const cs=[...String(href)];
  let i=0,j=cs.length;
  while(i<j&&cs[i].codePointAt(0)<=32)i++;
  while(j>i&&cs[j-1].codePointAt(0)<=32)j--;
  return cs.slice(i,j).filter(c=>c!=='\t'&&c!=='\n'&&c!=='\r').join('');
}
// RFC 3986 section 3.1: the scheme, when the first colon comes before any / ? # and what
// precedes it is a scheme. Only A-Z are lowered, as Lean's Char.toLower does.
const asciiLower=s=>s.replace(/[A-Z]/g,c=>c.toLowerCase());
function schemeOf(cs){
  const m=/^([^:/?#]*):/.exec(cs);
  return m&&/^[A-Za-z][A-Za-z0-9+.-]*$/.test(m[1])?asciiLower(m[1]):undefined;
}
// In a web or file address a backslash is a slash, up to the query or fragment.
function slashes(cs){
  const end=cs.search(/[?#]/),cut=end<0?cs.length:end;
  return cs.slice(0,cut).replace(/\\/g,'/')+cs.slice(cut);
}
function pageURL(site,name){
  return name==='settings'&&site.pages?new URL('settings.html',site.pages).href:'foafnaut:'+name;
}
function builtin(site,rest){
  const url='foafnaut:'+rest,slash=rest.indexOf('/');
  const name=slash<0?rest:rest.slice(0,slash),after=slash<0?'':rest.slice(slash),argument=after.slice(1);
  if(name==='graph')return after===''?{route:'graph',url:'foafnaut:graph'}:{route:'refuse',url,reason:'foafnaut:graph takes no argument'};
  if(builtinPages.has(name)){
    if(argument==='')return {route:'page',name,url:pageURL(site,name)};
    if(builtinPages.get(name))return {route:'page',name,url:`foafnaut:${name}/${argument}`};
    return {route:'refuse',url,reason:`foafnaut:${name} takes no argument`};
  }
  if(commands.includes(name))return {route:'command',name,argument};
  if(name==='help')return {route:'page',name:'settings',url:pageURL(site,'settings')};
  return {route:'refuse',url,reason:'this browser has no such page'};
}
// The checks of WebRoute.readHost, readPort and readWeb, on the authority as written.
function hostProblem(raw){
  const host=asciiLower(raw);
  if(host==='')return 'the address has no host';
  if(host.startsWith('['))return 'IPv6 hosts are not opened by this browser';
  if(!/^[a-z0-9._-]+$/.test(host))return 'the host has characters this browser does not read';
  const labels=host.split('.');
  if(labels.some(l=>l===''))return 'the host has an empty label';
  const last=labels[labels.length-1];
  const numeric=/^[0-9]+$/.test(last)||/^0x[0-9a-fA-F]*$/.test(last);
  const octet=l=>/^[0-9]+$/.test(l)&&(l==='0'||!l.startsWith('0'))&&Number(l)<=255;
  if(numeric&&!(labels.length===4&&labels.every(octet)))return 'numeric hosts other than a dotted quad are not opened';
}
function webProblem(authority,path){
  if(authority===undefined)return 'a web address needs // and a host';
  if(authority.includes('@'))return 'addresses with a user name are not followed';
  const colon=authority.indexOf(':');
  const host=colon<0?authority:authority.slice(0,colon),port=colon<0?'':authority.slice(colon+1);
  const bad=hostProblem(host);if(bad)return bad;
  if(port!==''&&!/^[0-9]+$/.test(port))return 'the port is not a number';
  if(port!==''&&Number(port)>65535)return 'the port is past 65535';
  return dotProblem(path);
}
function dotProblem(path){
  if(path.split('/').some(s=>{const l=asciiLower(s);return l.includes('%')&&['%2e','.%2e','%2e.','%2e%2e'].includes(l);}))
    return 'the path has an encoded dot segment';
}
// RFC 3986 parts of a reference: authority (after //) and path.
function parts(ref){
  const m=/^(?:([^:/?#]+):)?(?:\/\/([^/?#]*))?([^?#]*)/.exec(ref);
  return {scheme:m[1],authority:m[2],path:m[3]};
}
function decide(site,base,kind,url,scheme){
  if(kind==='web'){
    const origin=new URL(url).origin,host=new URL(url).hostname;
    if(site.origin&&origin===site.origin)return {route:'navigate',url};
    if(externalHosts.includes(host))return {route:'system',url};
    if(!site.origin)return {route:'navigate',url};
    return {route:'system',url};
  }
  if(kind==='file'){
    if(site.files&&schemeOf(clean(base))==='file')return {route:'navigate',url};
    return {route:'refuse',url,reason:'a web page can not open local files'};
  }
  if(systemSchemes.includes(scheme))return {route:'system',url};
  if(scheme==='javascript')return {route:'refuse',url,reason:'a link that runs a script is not followed'};
  if(scheme==='data')return {route:'refuse',url,reason:'data URLs are not opened as pages'};
  return {route:'refuse',url,reason:`this browser does not open ${scheme}: links`};
}
// A web or file address, absolute (`prepared` has a scheme) or relative to `base`.
function special_(site,base,prepared,scheme,cleaned){
  const own=parts(prepared),relative=scheme===undefined;
  // The authority is the href's own when it has one, else the page's.
  const authority=own.authority!==undefined||!relative?own.authority:parts(base).authority;
  const target=relative?schemeOf(clean(base)):scheme;
  let url;
  const refuse=reason=>({route:'refuse',url:cleaned,reason});
  if(target==='file'){
    const host=asciiLower(authority??'');
    if(host!==''&&host!=='localhost')return refuse('a file on another host is not opened');
    const bad=dotProblem(own.path);if(bad)return refuse(bad);
    try{url=new URL(prepared,base).href;}catch{return refuse('the address can not be read');}
    return decide(site,base,'file',url);
  }
  const bad=webProblem(authority,own.path);if(bad)return refuse(bad);
  try{url=new URL(prepared,base).href;}catch{return refuse('the address can not be read');}
  return decide(site,base,'web',url);
}

/** The route of WebRoute.route, for an engine that does not have the op. `site` is
{origin,pages,files}: origin is '' when the browser loads every web site itself. */
export function fallbackRoute({href,base='',origin='',pages='',files=false}){
  const site={origin,pages,files},cs=clean(href);
  if(cs.startsWith('foafnaut:'))return builtin(site,cs.slice(9));
  const scheme=schemeOf(cs);
  if(scheme==='foafnaut')return builtin(site,cs.slice(cs.indexOf(':')+1));
  if(scheme!==undefined&&special(scheme)){
    const prepared=slashes(cs);
    if(prepared.slice(prepared.indexOf(':'),prepared.indexOf(':')+3)!=='://')return {route:'refuse',url:cs,reason:'a web address needs // and a host'};
    return special_(site,base,prepared,scheme,cs);
  }
  if(scheme!==undefined){
    // The system gets the address as a URL parser writes it; a refused one is shown as written.
    if(!systemSchemes.includes(scheme))return decide(site,base,'other',scheme+cs.slice(cs.indexOf(':')),scheme);
    let url;try{url=new URL(cs).href;}catch{return {route:'refuse',url:cs,reason:'the address can not be read'};}
    return decide(site,base,'other',url,scheme);
  }
  const b=schemeOf(clean(base));
  if(b===undefined||!special(b))return {route:'refuse',url:cs,reason:noHost};
  return special_(site,base,slashes(cs),undefined,cs);
}

/** The router of a host: Lean's op when the engine has it (asked once), else
fallbackRoute. `call(request)` is the host's document call; it throws on an error answer.
`address` answers an address typed in the bar, or undefined for an engine without the op:
the host then keeps its older address handling. */
export function createRouter(call){
  let lean;
  const hasLean=()=>{
    if(lean===undefined){
      try{lean=call({op:'shellRoute',href:'foafnaut:graph',base:'',origin:'',pages:'',files:false}).route==='graph';}
      catch{lean=false;}
    }
    return lean;
  };
  return {
    route:request=>hasLean()?call({...request,op:'shellRoute'}):fallbackRoute(request),
    address:request=>hasLean()?call({...request,op:'shellRoute'}):undefined,
    get lean(){return hasLean();},
  };
}
