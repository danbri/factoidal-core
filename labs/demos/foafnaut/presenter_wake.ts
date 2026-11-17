// Coalesce wake messages without losing a publication made before an older wake's
// reply. The slot carries the value; this helper only arranges another read of it.
export function createBandWake(send:()=>Promise<unknown>,alive:()=>boolean){
  let newest=0n,pending=false;
  const wake=()=>{
    if(pending||!alive())return;
    pending=true;
    const notified=newest;
    send().finally(()=>{
      pending=false;
      // The worker may have read the slot before this publication. Its reply is
      // not an acknowledgement of values that were published after this wake.
      if(newest!==notified&&alive())wake();
    }).catch(()=>{});
  };
  return (sequence:bigint)=>{newest=sequence;wake();};
}
