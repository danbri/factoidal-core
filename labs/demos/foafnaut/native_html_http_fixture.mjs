// Controlled real HTTP input for desktop native-app qualification.
// Start with Node 22; no page parsing or rendering occurs in this server.
import http from 'node:http';
const port=Number(process.argv[2]??8116);
if(!Number.isInteger(port)||port<0||port>65535)throw Error('port must be 0..65535');
const requests=[];
const page=body=>'<!doctype html><style>body{margin:24px;font-family:monospace;font-size:24px;line-height:34px}h1{color:#184078}</style>'+body;
const source=page('<base href="/assets/"><link rel="stylesheet" href="theme.css"><h1>HTTP native HTML</h1><p>This page was fetched over HTTP. Resize to reflow these words.</p><p><a href="next.html">Follow the HTTP link</a></p>');
const server=http.createServer((request,response)=>{
  const url=new URL(request.url,'http://fixture.invalid');requests.push(url.pathname);
  console.log(JSON.stringify({type:'native-html-fixture-request',path:url.pathname}));
  if(url.pathname==='/requests.json'){response.setHeader('content-type','application/json');response.end(JSON.stringify(requests));return;}
  if(url.pathname==='/start'){response.writeHead(302,{location:'/pages/index.html'});response.end();return;}
  const routes={
    '/pages/index.html':['text/html; charset=utf-8',source],
    '/assets/theme.css':['text/css; charset=utf-8','a{color:#2050b0}'],
    '/assets/next.html':['text/html; charset=utf-8',page('<h1>Second HTTP page</h1><p><a href="/start">Return through the redirect</a></p>')],
    '/blocked.html':['text/html; charset=utf-8',page('<link rel="stylesheet" href="file:///etc/passwd"><p>Must be refused before reading any local stylesheet.</p>')],
  };
  const row=routes[url.pathname];
  if(!row){response.writeHead(404);response.end('missing');return;}
  response.setHeader('content-type',row[0]);response.end(row[1]);
});
server.listen(port,'127.0.0.1',()=>console.log(JSON.stringify({type:'native-html-fixture-ready',url:`http://127.0.0.1:${server.address().port}/start`})));
process.on('SIGTERM',()=>server.close());
process.on('SIGINT',()=>server.close());
