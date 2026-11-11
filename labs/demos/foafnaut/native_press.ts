// Native input bookkeeping only. The engine owns hit testing and click decisions.
export const POINTER_CANCEL=14;
export type PointerKind="down"|"move"|"up"|"cancel";
type HitRequest={width:number;height:number;options:Record<string,unknown>};
export type PresentedState<Page>=HitRequest&{document:Page;scroll:number};
export function pointerRequest<Page>(page:Page,presented:PresentedState<Page>|undefined,fallback:()=>HitRequest):HitRequest{
  // Before this page has a presented frame (or after a tab change), retain the
  // existing request path; another page's visible state cannot describe its layout.
  if(!presented||presented.document!==page)return fallback();
  const {width,height,options,scroll}=presented;
  return {width,height,options:{...options,shell:{...options.shell as Record<string,unknown>,scroll}}};
}
export type NativePress<Page>={page:Page;points:number[];node?:number};
export function beginPress<Page>(page:Page,x:number,y:number):NativePress<Page>{
  return {page,points:[x,y,x,y]};
}
export function movePress<Page>(press:NativePress<Page>,x:number,y:number){
  press.points=[press.points[0],press.points[1],x,y];
  return press.points;
}
export function pointerNode<Page>(press:NativePress<Page>,kind:PointerKind,node:number|null){
  if(kind==="down")press.node=typeof node==="number"?node:undefined;
  return typeof node==="number"?node:kind==="up"||kind==="cancel"?press.node:undefined;
}
// A down hit test must finish before its release can use the saved node. Moves
// still wait for idle input; down, up and cancel are always kept, even after an error.
export function pressPointers(){
  let tail=Promise.resolve(),pending=0;
  return (kind:PointerKind,run:()=>Promise<void>)=>{
    if(kind==="move"&&pending)return Promise.resolve();
    pending++;
    const next=tail.then(run).finally(()=>{pending--;});
    tail=next.catch(()=>{});
    return next;
  };
}
// Once a press waits for the first frame, all following input waits behind it.
// Keep stamps with events, and drain even when the next native batch is empty.
export function beforeFirstFrame<T extends {event:{kind:number}}>(){
  let waiting:T[]=[];
  // Close, resize and occlusion do not wait: the first frame may need them.
  const held=(item:T)=>![1,6,8].includes(item.event.kind);
  return (batch:T[],presented:boolean)=>{
    if(presented){const ready=[...waiting,...batch];waiting=[];return ready;}
    if(waiting.length){waiting.push(...batch.filter(held));return batch.filter(item=>!held(item));}
    const down=batch.findIndex(item=>item.event.kind===2);
    if(down<0)return batch;
    const later=batch.slice(down);
    waiting=later.filter(held);return [...batch.slice(0,down),...later.filter(item=>!held(item))];
  };
}
