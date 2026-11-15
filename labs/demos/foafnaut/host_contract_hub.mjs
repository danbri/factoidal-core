// host_contract_hub.mjs: the Hub's Textnaut host (docs/web/hub/textnaut/engine-core.mjs, the code
// the Hub page runs in its worker) run headless in Node on the Wasm build, with its boundary trace
// recorded at the module's `ccall` (docs/web/hub/foafnaut/host-trace.mjs). Used by
// host_contract_check.ts. The page is given as HTML, as the Hub's notebook gives pasted markup.
//   node host_contract_hub.mjs PAGE.html TRACE.jsonl [COLS]
// HUB_RUNTIME names the directory of web-render.mjs and web-render.wasm.
import fs from 'node:fs';
import {nodeHost} from '../../../tests/hub/_textnaut_host.mjs';
import {createEngineCore} from '../../../docs/web/hub/textnaut/engine-core.mjs';
import {traceModule} from '../../../docs/web/hub/foafnaut/host-trace.mjs';

const [page,tracePath,cols='80']=process.argv.slice(2);
if(!page||!tracePath){console.error('usage: node host_contract_hub.mjs PAGE.html TRACE.jsonl [COLS]');process.exit(2);}
fs.writeFileSync(tracePath,'');
const host=await nodeHost();
const createModule=host.createModule;
host.createModule=async options=>traceModule(await createModule(options),line=>fs.appendFileSync(tracePath,JSON.stringify(line)+'\n'));
const core=createEngineCore(host);
const out=await core.textGrid('page',{html:fs.readFileSync(page,'utf8'),url:`${host.origin}/host-contract/page.html`},{cols:Number(cols),scripts:true});
console.log(JSON.stringify({rows:out.rows?.length??out.text?.split('\n').length??0,scripts:out.scripts?.turns??null}));
