/** Single-writer, latest-wins transport for Presenter.Spec's channels.
 *
 * Layout (bytes): 0..7 unsigned 64-bit seqlock; 8..11 payload length;
 * 12..15 immutable capacity; 16.. payload, padded to a word boundary.
 * Zero means no publication, odd means writing, even means committed. A
 * publication's sequence is the even value / 2. Exhaustion is refused, never
 * wrapped: a stalled reader cannot mistake a later publication for its first.
 * All shared reads and writes, including payload words, are Atomics operations.
 *
 * A successful read linearises at its second version read. With unchanged even
 * versions it returns the latest completed publication at that point. A busy
 * result is NOT a delivery: the caller retains its last frame and polls later.
 * Thus successful frame reads meet LatestWins; at quiescence a successful
 * request read meets LastRequestSeen. Eventual polling after the final write is
 * a scheduling assumption, not a property this transport can enforce.
 *
 * Storage is capacity + at most 19 bytes. Reading copies at most capacity bytes;
 * publishing and reading do O(ceil(length / 4)) work with constant stack. The
 * caller chooses capacity from its engine's resource limit. Oversize publication
 * fails before changing the slot. This module makes no page or presenter decisions.
 */
const HEADER_BYTES=16;
const LAST_VERSION=(1n<<64n)-2n;
type Views={version:BigUint64Array;header:Uint32Array;words:Uint32Array;capacity:number};
const attached=new WeakMap<SharedArrayBuffer,Views>();

function views(buffer:SharedArrayBuffer):Views {
  let v=attached.get(buffer);
  if(v)return v;
  if(buffer.byteLength<HEADER_BYTES||buffer.byteLength%4!==0)throw new Error("Invalid presenter slot layout");
  const header=new Uint32Array(buffer,8,2),capacity=Atomics.load(header,1);
  if(capacity>buffer.byteLength-HEADER_BYTES)throw new Error("Invalid presenter slot capacity");
  v={version:new BigUint64Array(buffer,0,1),header,words:new Uint32Array(buffer,HEADER_BYTES),capacity};
  attached.set(buffer,v);return v;
}

export type SlotRead<T>={status:"value";sequence:bigint;value:T}|{status:"empty"}|{status:"busy"}|{status:"unchanged"};
export type ByteSlotRead={status:"value";sequence:bigint;bytes:Uint8Array}|{status:"empty"}|{status:"busy"}|{status:"unchanged"};

export function createByteSlot(capacity:number):SharedArrayBuffer {
  if(!Number.isSafeInteger(capacity)||capacity<0||capacity>0x7fffffec)throw new RangeError("Invalid presenter slot capacity");
  const buffer=new SharedArrayBuffer(HEADER_BYTES+4*Math.ceil(capacity/4));
  Atomics.store(new Uint32Array(buffer,8,2),1,capacity);
  return buffer;
}

/** Source bytes must remain unchanged until this synchronous call returns.
 * Only one writer owns a slot. CAS also refuses an overlapping second writer. */
export function publishBytes(buffer:SharedArrayBuffer,bytes:Uint8Array):bigint {
  const v=views(buffer);
  if(bytes.byteLength>v.capacity)throw new RangeError(`Presenter slot capacity ${v.capacity} exceeded by ${bytes.byteLength} bytes`);
  if(bytes.buffer===buffer)throw new Error("Presenter slot cannot publish from itself");
  const source=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  const before=Atomics.load(v.version,0);
  if(before&1n)throw new Error("Presenter slot already has a writer");
  if(before===LAST_VERSION)throw new RangeError("Presenter slot sequence exhausted");
  if(Atomics.compareExchange(v.version,0,before,before+1n)!==before)throw new Error("Presenter slot has multiple writers");
  let offset=0;
  for(;offset+4<=bytes.length;offset+=4)Atomics.store(v.words,offset/4,source.getUint32(offset,true));
  if(offset<bytes.length){
    let word=0;for(let b=0;offset+b<bytes.length;b++)word|=bytes[offset+b]<<(8*b);
    Atomics.store(v.words,offset/4,word>>>0);
  }
  Atomics.store(v.header,0,bytes.length);
  const committed=before+2n;
  Atomics.store(v.version,0,committed);
  return committed/2n;
}

/** One attempt, with no retry or wait on the presenter thread. Matching
 * afterSequence returns unchanged before copying or allocating the payload. */
export function readBytes(buffer:SharedArrayBuffer,afterSequence?:bigint):ByteSlotRead {
  const v=views(buffer),before=Atomics.load(v.version,0);
  if(before===0n)return {status:"empty"};
  if(before&1n)return {status:"busy"};
  if(afterSequence===before/2n)return {status:"unchanged"};
  const length=Atomics.load(v.header,0);
  if(length>v.capacity)throw new Error("Presenter slot length exceeds capacity");
  const bytes=new Uint8Array(length),target=new DataView(bytes.buffer);
  let offset=0;
  for(;offset+4<=length;offset+=4)target.setUint32(offset,Atomics.load(v.words,offset/4),true);
  if(offset<length){
    const word=Atomics.load(v.words,offset/4);
    for(let b=0;offset+b<length;b++)bytes[offset+b]=(word>>>(8*b))&255;
  }
  if(Atomics.load(v.version,0)!==before)return {status:"busy"};
  return {status:"value",sequence:before/2n,bytes};
}

export function createRequestSlot():SharedArrayBuffer {return createByteSlot(8);}
export function publishRequest(buffer:SharedArrayBuffer,value:number):bigint {
  if(!Number.isSafeInteger(value)||value<0)throw new RangeError("Presenter request must be a nonnegative safe integer");
  const bytes=new Uint8Array(8);new DataView(bytes.buffer).setBigUint64(0,BigInt(value),true);
  return publishBytes(buffer,bytes);
}
export function readRequest(buffer:SharedArrayBuffer,afterSequence?:bigint):SlotRead<number> {
  const result=readBytes(buffer,afterSequence);
  if(result.status!=="value")return result;
  if(result.bytes.length!==8)throw new Error("Invalid presenter request length");
  const value=Number(new DataView(result.bytes.buffer).getBigUint64(0,true));
  if(!Number.isSafeInteger(value))throw new Error("Invalid presenter request value");
  return {status:"value",sequence:result.sequence,value};
}
