// The GPU work of one Lean scene draw, counted from the scene itself (core issue 450): a
// measurement for hub_spinal_perf.mjs and spinal_perf.ts, not part of drawing. It reads the
// scene's storage rows and tile words as the scene shader (SVG.lean sceneShader) reads them and
// counts, for the pixels the host draws (the damage rectangles of a partial draw, or the whole
// scene), what the fragment shader does per sample:
//
// - `listed`: primitive records visited (each tile's list, for each pixel of the tile);
// - `segments`: path and polygon edges the winding loop walks (it walks every edge of a path or
//   polygon for each sample inside the record's bounds);
// - `segmentsOutsideClip`: edges of records in tiles that lie wholly outside one of the
//   record's clip rectangles. A shader that goes to the next record when the clip fails (its
//   text has `if(!clipHit){continue;}`, `skipsClipped`) does not walk them, and they are not in
//   `segments`; an older shader walks them and drops the result, and they are. A scene with
//   tile edge lists (its shader has `fn pathWinding(`) walks only the tile's list of a path;
// - `pieces`: stroke pieces tested (a stroke is drawn as a union of strips, disks and
//   triangles; the tile's piece list when the scene has one, else every piece; an upper
//   bound, as the shader stops at the first piece that holds the sample). A tile's list in
//   cell form (CELL_MARK: SVG.lean tileCells, edgeBands) is walked per cell of a 4x4 grid of
//   the tile for pieces, per row band for edges;
// - `segmentsBinned`: what `segments` would be if each tile walked only the edges of a record
//   that can change the winding number differently across that tile (an edge whose rows meet
//   the tile's and that is not wholly left of it, less an edge wholly right of it that spans
//   all its rows, which adds the same to every sample there): the work of per-tile edge lists.
//
// Counts are per sample at four samples a pixel (the first pass; an edge pixel takes sixteen),
// and whole tiles are judged by their corners, so they are estimates of the shader's loop
// trips, exact for the record lists and the drawn area. Also: `uploadBytes` (storage floats and
// tile words written each draw), `drawnPixels`, `tiles`, `tileEntries`.
const ALL_EDGES=4294967295,CELL_MARK=4294967294,CELLS=4,SAMPLES=4,FIXED_ROWS=5,DASH_ROWS=5,CLIP_ROWS=3,AFFINE_ROWS=2,PATH=6,POLYGON=5;

/** Work of drawing `frame` (an artifact: width, height, data, tiles, damage) over `rects`
(damage rectangles [x,y,w,h]; undefined for a full draw). */
export function sceneWork(frame,rects){
  const data=frame.data,tiles=frame.tiles,width=frame.width,height=frame.height;
  const out={uploadBytes:(data?.length??0)*4+(tiles?.length??0)*4,drawnPixels:0,tiles:0,tileEntries:0,listed:0,segments:0,segmentsOutsideClip:0,
    partial:!!rects,maxSegmentsPerSample:0,segmentsBinned:0,segmentsRows:0,pieces:0,skipsClipped:typeof frame.wgsl==='string'&&frame.wgsl.includes('if(!clipHit){continue;}'),
    // Tile edge lists (tilesOf): each listed record has a list word after the entries.
    edgeLists:typeof frame.wgsl==='string'&&frame.wgsl.includes('fn pathWinding('),
    // Stroke piece lists after the edge part of each record (a shader with `var listed=false`).
    pieceLists:typeof frame.wgsl==='string'&&frame.wgsl.includes('var listed=false')};
  if(!data||!tiles||tiles.length<4)return out;
  const row=i=>[data[4*i],data[4*i+1],data[4*i+2],data[4*i+3]];
  const rowCount=data.length/4;
  if(rowCount<2)return out;
  const [sx,sy,ox,oy]=row(0),[wx,wy]=row(1);
  const world=(x,y)=>[(x-ox)/sx+wx,(y-oy)/sy+wy];
  const size=tiles[0],across=tiles[1],down=tiles[2],listBase=4+across*down,refBase=listBase+tiles[3+across*down];
  out.tiles=across*down;out.tileEntries=tiles[3+across*down]-tiles[3];
  // Pixels of each tile that are drawn: all of it, or its part inside the damage rectangles.
  const drawn=(x0,y0,x1,y1)=>{
    if(!rects)return (x1-x0)*(y1-y0);
    let n=0;for(const [rx,ry,rw,rh] of rects){const w=Math.min(x1,rx+rw)-Math.max(x0,rx),h=Math.min(y1,ry+rh)-Math.max(y0,ry);if(w>0&&h>0)n+=w*h;}
    return n;
  };
  // The box of the tile's corners through an affine map [a,b,c] [d,e,f].
  const mapBox=(corners,x,y)=>{let x0=Infinity,y0=Infinity,x1=-Infinity,y1=-Infinity;
    for(const [u,v] of corners){const p=x[0]*u+x[1]*v+x[2],q=y[0]*u+y[1]*v+y[2];x0=Math.min(x0,p);x1=Math.max(x1,p);y0=Math.min(y0,q);y1=Math.max(y1,q);}
    return [x0,y0,x1,y1];};
  for(let t=0;t<across*down;t++){
    const tx=(t%across)*size,ty=Math.floor(t/across)*size;
    const px=drawn(tx,ty,Math.min(width,tx+size),Math.min(height,ty+size));
    // Pixels drawn in each row band and each cell of the tile (cell form lists).
    const cs=size/CELLS,cellPx=[],bandPx=[];
    for(let cy=0;cy<CELLS;cy++){let b=0;for(let cx=0;cx<CELLS;cx++){
      const x0=tx+cx*cs,y0=ty+cy*cs,n=x0<width&&y0<height?drawn(x0,y0,Math.min(width,x0+cs),Math.min(height,y0+cs)):0;cellPx.push(n);b+=n;}bandPx.push(b);}
    if(!px)continue;
    out.drawnPixels+=px;
    const samples=px*SAMPLES;
    const corners=[world(tx,ty),world(tx+size,ty),world(tx,ty+size),world(tx+size,ty+size)];
    let perSample=0;
    for(let item=tiles[3+t];item<tiles[4+t];item++){
      const base=tiles[listBase+item];
      if(base+FIXED_ROWS>rowCount)break;
      out.listed+=samples;
      const [tag,count,,w]=row(base+1);
      // Stroke pieces (a stroke is a union of pieces): the tile's piece list, else all of them.
      const [,,dashCount,dashed]=row(base+4);
      const word=out.edgeLists?tiles[refBase+item]:ALL_EDGES;
      if(dashed===1){
        let n=dashCount,cells;
        if(out.pieceLists&&word!==ALL_EDGES){const ne=tiles[word],pl=ne===ALL_EDGES?word+1:ne===CELL_MARK?word+2+CELLS+tiles[word+1+CELLS]:word+1+ne;
          if(tiles[pl]===CELL_MARK)cells=pl;else if(tiles[pl]!==ALL_EDGES)n=Math.min(tiles[pl],dashCount);}
        if(cells!==undefined)for(let c=0;c<CELLS*CELLS;c++)out.pieces+=cellPx[c]*SAMPLES*Math.min(tiles[cells+2+c]-tiles[cells+1+c],dashCount);
        else out.pieces+=samples*n;
      }
      if(tag!==PATH&&tag!==POLYGON)continue;
      const shapeRows=tag===PATH?count:Math.ceil(count/2),clipCount=Math.floor(w/4);
      const tailRows=shapeRows+DASH_ROWS*dashCount,affine=(w%4)>=2;
      let box=corners;
      if(affine){const ax=row(base+FIXED_ROWS+tailRows),ay=row(base+FIXED_ROWS+tailRows+1);const b=mapBox(corners,ax,ay);box=[[b[0],b[1]],[b[2],b[3]]];}
      const [bx0,by0,bx1,by1]=row(base);
      const xs=box.map(c=>c[0]),ys=box.map(c=>c[1]);
      // withinBounds: no edge is walked where the tile misses the record's bounds.
      if(Math.max(...xs)<bx0||Math.min(...xs)>bx1||Math.max(...ys)<by0||Math.min(...ys)>by1)continue;
      const clipBase=base+FIXED_ROWS+tailRows+(affine?AFFINE_ROWS:0);
      let outside=false;
      for(let c=0;c<clipCount;c++){
        const cx=row(clipBase+CLIP_ROWS*c),cy=row(clipBase+CLIP_ROWS*c+1),[qx,qy,qw,qh]=row(clipBase+CLIP_ROWS*c+2);
        const [x0,y0,x1,y1]=mapBox(corners,cx,cy);
        if(cx[3]!==1||x1<qx||x0>qx+qw||y1<qy||y0>qy+qh){outside=true;break;}
      }
      if(outside){out.segmentsOutsideClip+=samples*count;if(out.skipsClipped)continue;}
      // A path's fill walks the tile's edge list when the scene has them.
      if(tag===PATH&&word!==ALL_EDGES&&tiles[word]===CELL_MARK){
        let most=0;for(let b=0;b<CELLS;b++){const n=Math.min(tiles[word+2+b]-tiles[word+1+b],count);out.segments+=bandPx[b]*SAMPLES*n;most=Math.max(most,n);}
        perSample+=most;
      }else{
        const walked=tag!==PATH||word===ALL_EDGES||tiles[word]===ALL_EDGES?count:Math.min(tiles[word],count);
        out.segments+=samples*walked;perSample+=walked;
      }
      // The edges this tile would keep (tile box in the record's space).
      const X0=Math.min(...xs),X1=Math.max(...xs),Y0=Math.min(...ys),Y1=Math.max(...ys);
      let kept=0,rows=0;
      for(let k=0;k<count;k++){
        let ax,ay,bx,by;
        if(tag===PATH){const r=4*(base+FIXED_ROWS+k);ax=data[r];ay=data[r+1];bx=data[r+2];by=data[r+3];}
        else{const a=4*(base+FIXED_ROWS)+2*k,b=4*(base+FIXED_ROWS)+2*((k+1)%count);ax=data[a];ay=data[a+1];bx=data[b];by=data[b+1];}
        const y0=Math.min(ay,by),y1=Math.max(ay,by);
        if(y1<Y0||y0>Y1)continue;
        rows++;
        if(Math.max(ax,bx)<X0)continue;
        if(Math.min(ax,bx)>X1&&y0<=Y0&&y1>=Y1)continue;
        kept++;
      }
      // Per-tile edge lists with the clip skip: a tile outside the clip lists nothing.
      if(!outside){out.segmentsBinned+=samples*kept;out.segmentsRows+=samples*rows;}
    }
    out.maxSegmentsPerSample=Math.max(out.maxSegmentsPerSample,perSample);
  }
  return out;
}
