import {createServer} from 'node:http';
export function makeNavigationFixture(){
 const requests=[];
 const pages={
  '/one':'<!doctype html><style>body{margin:0;font-size:16px;line-height:24px}a{color:blue}</style><p>First page</p><a href="two?from=one">Next page</a>',
  '/two':'<!doctype html><style>body{margin:0;font-size:16px;line-height:24px}</style><p>Second page</p><a href="/one">First page</a>',
  '/sheet':'<!doctype html><link rel="stylesheet" href="/sheet.css"><p>External sheet</p>',
  '/sheet.css':'body{background:red}',
  '/dynamic':'<!doctype html><base href="/nested/"><link rel="stylesheet" href="../dynamic.css"><p id="message">Before</p><a id="change" href="#changed">Change text</a><br><a href="../two">Next page</a><script src="../dynamic.js"></script>',
  '/dynamic.css':'body{margin:0;font-family:Arial;font-size:16px;line-height:24px;background:#f0f8ff}a{color:blue}',
  '/dynamic.js':"let count=0;document.getElementById('message').textContent='Loaded';document.getElementById('change').addEventListener('click',()=>{count++;document.getElementById('message').textContent='Count '+count;});",
  '/slow':'<!doctype html><p>Slow page</p>',
  '/bad-utf8':Buffer.from([0xff,0xfe,0x61]),
  '/large':'x'.repeat(1048577),
 };
 const server=createServer((req,res)=>{
  requests.push(req.url);const path=new URL(req.url,'http://fixture.test').pathname;
  if(path==='/redirect'){res.writeHead(302,{Location:'/two?redirected=1'});res.end();return;}
  if(path==='/loop'){res.writeHead(302,{Location:'/loop'});res.end();return;}
  if(!(path in pages)){res.writeHead(404);res.end('Missing fixture');return;}
  const respond=()=>{if(res.destroyed)return;res.writeHead(200,{'Content-Type':path.endsWith('.css')?'text/css':path.endsWith('.js')?'text/javascript':'text/html; charset=utf-8'});res.end(pages[path]);};
  if(path==='/slow')setTimeout(respond,250);else respond();
 });return {server,requests,pages};
}
