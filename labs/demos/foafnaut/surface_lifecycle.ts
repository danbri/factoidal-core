export type SurfaceDriver<T> = {
  configure(width:number,height:number):void;
  prepare():void;
  acquire():T;
  present():void;
  state?():unknown;
  ready?():boolean;
};

// Presentation transport only. A failed acquire/present is reported once with
// stage/state; there is deliberately no blind retry or swallowed GPU failure.
export class SurfaceLifecycle<T> {
  private width=0;
  private height=0;
  framesPresented=0;
  constructor(private driver:SurfaceDriver<T>,private format:string,
    private log:(message:string,details:unknown)=>void=(message,details)=>console.log(message,details)) {}
  private snapshot() {
    let native:unknown;
    try { native=this.driver.state?.(); } catch(error) { native={snapshotError:String(error)}; }
    return {framesPresented:this.framesPresented,width:this.width,height:this.height,format:this.format,native};
  }
  configure(width:number,height:number) {
    this.width=width;this.height=height;
    this.driver.configure(width,height);
    this.driver.prepare();
    this.log("Native surface configured (CA transaction flushed)",this.snapshot());
  }
  acquire():T|null {
    if(this.driver.ready && !this.driver.ready())return null;
    if(this.framesPresented===0)this.log("Native surface acquiring first texture",this.snapshot());
    try { return this.driver.acquire(); }
    catch(error) { throw new Error(`Native surface acquire failed: ${JSON.stringify(this.snapshot())}`,{cause:error}); }
  }
  present() {
    try { this.driver.present(); }
    catch(error) { throw new Error(`Native surface present failed: ${JSON.stringify(this.snapshot())}`,{cause:error}); }
    this.framesPresented++;
    if(this.framesPresented===1)this.log("Native surface first frame presented",this.snapshot());
  }
}
