// Navigation/history transport only. Targets come from the address bar or
// Lean's link picker. Document parsing and link discovery remain in Lean.
export function navigationURL(value,base){
  const input=String(value).trim();if(!input)throw Error('Enter an HTTP or HTTPS URL');
  let url;try{url=new URL(input,base);}catch{throw Error('Enter a complete HTTP or HTTPS URL');}
  if(!['http:','https:'].includes(url.protocol))throw Error(`Navigation scheme ${url.protocol} is not supported`);
  if(url.username||url.password)throw Error('URLs with credentials are not supported');
  return url.href;
}
export class NavigationController {
  constructor({load,render,onState=()=>{}}){this.load=load;this.render=render;this.onState=onState;this.entries=[];this.index=-1;this.sequence=0;this.loading=false;}
  snapshot(){return {url:this.entries[this.index]?.url??null,index:this.index,entries:this.entries.map(e=>e.url),canBack:this.index>0,canForward:this.index+1<this.entries.length,loading:this.loading};}
  emit(extra={}){this.onState({...this.snapshot(),...extra});}
  cancel(){this.sequence++;this.abort?.abort();this.abort=undefined;this.loading=false;this.emit({cancelled:true});}
  async go(value,{history='push',index,base=this.snapshot().url}={}){
    let url;try{url=navigationURL(value,base??undefined);}catch(error){this.sequence++;this.abort?.abort();this.abort=undefined;this.loading=false;this.emit({error:error.message});return false;}
    const request=++this.sequence;this.abort?.abort();const controller=this.abort=new AbortController();
    this.loading=true;this.emit({requestedURL:url});
    const isCurrent=()=>request===this.sequence&&!controller.signal.aborted;
    try{
      const resource=await this.load(url,{signal:controller.signal});if(!isCurrent())return false;
      // Redirect response URLs omit the fragment; retain it for document identity.
      const finalURL=new URL(resource.url);if(!finalURL.hash)finalURL.hash=new URL(url).hash;
      await this.render(resource,{url:finalURL.href,signal:controller.signal,isCurrent});if(!isCurrent())return false;
      const entry={url:finalURL.href};
      if(history==='traverse'){this.entries[index]=entry;this.index=index;}
      else if(history==='replace'&&this.index>=0)this.entries[this.index]=entry;
      else{this.entries=this.entries.slice(0,this.index+1);this.entries.push(entry);this.index++;}
      this.loading=false;this.emit({committed:true});return true;
    }catch(error){if(!isCurrent())return false;this.loading=false;this.emit({error:String(error.message??error),requestedURL:url});return false;}
    finally{if(request===this.sequence)this.abort=undefined;}
  }
  back(){return this.index>0?this.go(this.entries[this.index-1].url,{history:'traverse',index:this.index-1}):Promise.resolve(false);}
  forward(){return this.index+1<this.entries.length?this.go(this.entries[this.index+1].url,{history:'traverse',index:this.index+1}):Promise.resolve(false);}
  reload(){const url=this.snapshot().url;return url?this.go(url,{history:'replace'}):Promise.resolve(false);}
}
