import {boundedFetch} from './bounded-fetch.mjs';
import {discoverPods,createPodStorage} from './pod-storage.mjs';
import {decodePipelineDocument,MAX_PIPELINE_BYTES} from './pipeline-document.mjs';

// Reuse the compositor worker's engine. Only the shared LWS client moves HTTP
// bytes; its Lean state machine owns authentication and request semantics.
export function createStorageHandler(getCore, clientModule = () => import('../runtime/lws/client.mjs')) {
  const clients=new Map();
  const transport=boundedFetch((...args)=>fetch(...args),MAX_PIPELINE_BYTES);
  return async function storage(operation,args={}) {
    if(operation==='discover'&&args.bearer)throw Error('Bootstrap discovery uses no pod credential.');
    if(operation==='forget'){clients.clear();return {forgotten:true};}
    const core=await getCore();
    const root=args.pod?.url;
    if(args.bearer && (!root || args.bearer.realm!==root))throw Error('The token realm must be the selected pod.');
    const key=JSON.stringify([root??null,args.bearer??null]);
    let client=clients.get(key);
    if(!client){const {createLwsClient}=await clientModule();client=await createLwsClient({engine:await core.loadEngine(),fetch:transport,...(args.bearer?{bearer:args.bearer}:{})});clients.set(key,client);}
    if(operation==='discover')return discoverPods({core,client,bootstrapUrl:args.bootstrapUrl});
    if(!args.pod || typeof args.pod!=='object')throw Error('Select a discovered pod first.');
    const store=createPodStorage({core,client,root:args.pod});
    if(operation==='list')return store.list(args.url);
    if(operation==='load')return store.load(args.url);
    if(operation==='save'){
      decodePipelineDocument(args.text); // do not save credentials/arbitrary objects as pipelines
      return store.save(args.url,args.text,{etag:args.etag,create:args.create});
    }
    throw Error('Unknown pipeline storage operation.');
  };
}
