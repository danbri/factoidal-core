// Lossless byte transport only: no geometry, drawing or color conversion.
import {deflateSync} from 'node:zlib';
const table=Array.from({length:256},(_,n)=>{for(let i=0;i<8;i++)n=n&1?0xedb88320^(n>>>1):n>>>1;return n>>>0;});
function chunk(kind,payload){
 const name=Buffer.from(kind),body=Buffer.concat([name,payload]),out=Buffer.alloc(body.length+8);out.writeUInt32BE(payload.length);body.copy(out,4);
 let crc=0xffffffff;for(const byte of body)crc=table[(crc^byte)&255]^(crc>>>8);out.writeUInt32BE((crc^0xffffffff)>>>0,out.length-4);return out;
}
export function encodeRGBA(width,height,rgba){
 if(!Number.isInteger(width)||!Number.isInteger(height)||width<1||height<1||width>4096||height>4096||rgba.length!==width*height*4)throw Error('Invalid bounded RGBA raster');
 const header=Buffer.alloc(13);header.writeUInt32BE(width);header.writeUInt32BE(height,4);header[8]=8;header[9]=6;
 const scan=Buffer.alloc((width*4+1)*height);
 for(let y=0;y<height;y++)Buffer.from(rgba.buffer,rgba.byteOffset+y*width*4,width*4).copy(scan,y*(width*4+1)+1);
 return Buffer.concat([Buffer.from([137,80,78,71,13,10,26,10]),chunk('IHDR',header),chunk('IDAT',deflateSync(scan,{level:9})),chunk('IEND',Buffer.alloc(0))]);
}
