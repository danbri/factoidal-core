// Scroll prefetch for the two-layer view (issue 1268). Pure rules, with no window and no
// engine, so the tests can run them. run_html.ts applies them.
//
// A band of Lean's (WebDocument.band) keeps the scrolls keepFrom..keepTo with no new
// render. When the scroll comes near an edge of that range, or its speed says it will
// leave the range before a new band can be made, the host asks the worker, at low
// priority, for the next band. When the scroll leaves the range, the host shows that
// band with no Lean wait, if it was made for the same document state.
import type {HTMLLayerPlace} from "./native_html_engine.ts";

export type Band=Pick<HTMLLayerPlace,"view"|"bandTop"|"bandHeight"|"keepFrom"|"keepTo">;

/** Rows that a band made at scroll s keeps on each side of s, read from Lean's answer:
 * the margin (bandHeight-view)/2 less the refresh margin bandTop+bandHeight-view-keepTo.
 * For WebDocument.band this is 512-128 = 384 rows, at the top of the page too. */
export function keepReach(band:Band):number {
  const margin=Math.floor((band.bandHeight-band.view)/2);
  const refresh=band.bandTop+band.bandHeight-band.view-band.keepTo;
  return Math.max(0,margin-refresh);
}

/** Scroll speed and direction from the scroll events. */
export type Motion={direction:-1|0|1;rowsPerMs:number;scroll:number;at:number};
/** A pause longer than this ends a motion. */
export const MOTION_GAP_MS=250;
export function trackMotion(previous:Motion|undefined,scroll:number,at:number):Motion {
  if(!previous||at-previous.at>MOTION_GAP_MS)return {direction:0,rowsPerMs:0,scroll,at};
  const delta=scroll-previous.scroll;
  if(delta===0)return {...previous,at};
  const direction=delta>0?1:-1,instant=Math.abs(delta)/Math.max(1,at-previous.at);
  // Half the old speed and half the new one; a turn starts again from the new speed.
  const rowsPerMs=direction===previous.direction?(previous.rowsPerMs+instant)/2:instant;
  return {direction,rowsPerMs,scroll,at};
}

export type PrefetchRule={
  /** Ask when the scroll is this many rows or fewer from the edge of the keep range. */
  marginRows:number;
  /** Ask when the motion will reach the edge within this time: two frames and the time a band takes. */
  horizonMs:number;
  /** The largest scroll of the page. */
  limit:number;
};
export const PREFETCH_MARGIN_ROWS=256;
export const FRAME_MS=1000/60;

/** The scroll to make the next band at, or undefined when no prefetch is due.
 * The next band starts its keep range where this one ends: down, its keepFrom is this
 * keepTo; up, its keepTo is this keepFrom. With no motion, or a scroll already out of
 * the range (the ordinary frame path then answers), or a band that already reaches the
 * page edge, there is no prefetch. */
export function prefetchTarget(band:Band,scroll:number,motion:Motion,rule:PrefetchRule):number|undefined {
  if(motion.direction===0)return undefined;
  if(scroll<band.keepFrom||scroll>band.keepTo)return undefined;
  const reach=keepReach(band);
  if(reach<=0)return undefined;
  const down=motion.direction>0;
  if(down?band.keepTo>=rule.limit:band.keepFrom<=0)return undefined;
  const distance=down?band.keepTo-scroll:scroll-band.keepFrom;
  if(distance>rule.marginRows&&motion.rowsPerMs*rule.horizonMs<distance)return undefined;
  const target=down?band.keepTo+reach:band.keepFrom-reach;
  return Math.max(0,Math.min(rule.limit,target));
}

/** The document state a render request is for, with the scroll left out: a band made for
 * one state shows any scroll in its keep range for that state and no other. Large values
 * are compared by identity (the resources) or by value (the graph model), not as JSON. */
export type StateKey={document:unknown;width:number;height:number;resources:unknown;graphModel:unknown;rest:string};
export function stateKey(document:unknown,options:Record<string,unknown>,width:number,height:number):StateKey {
  const {resources,graphModel,shell,...rest}=options;
  let shellRest:unknown=shell;
  if(shell&&typeof shell==="object"){const {scroll:_scroll,...others}=shell as Record<string,unknown>;shellRest=others;}
  return {document,width,height,resources,graphModel,rest:JSON.stringify([rest,shellRest])};
}
export function sameState(a:StateKey,b:StateKey):boolean {
  return a.document===b.document&&a.width===b.width&&a.height===b.height&&a.resources===b.resources&&a.graphModel===b.graphModel&&a.rest===b.rest;
}

/** True when a prefetched band can be shown at `scroll` in place of a Lean frame: the same
 * state, the scroll in its keep range, and the band on screen no longer keeps the scroll. */
export function canSwap(shownBand:Band,prefetched:{key:StateKey;band:Band},now:StateKey,scroll:number):boolean {
  const keptNow=scroll>=shownBand.keepFrom&&scroll<=shownBand.keepTo;
  const keptNext=scroll>=prefetched.band.keepFrom&&scroll<=prefetched.band.keepTo;
  return !keptNow&&keptNext&&sameState(prefetched.key,now);
}
