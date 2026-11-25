// The Hub draws the page on a canvas, where a screen reader finds nothing. This module keeps one
// hidden element for each node of the engine's accessibility tree (op accessibilityTree with
// web: true; HTML/AccessibleTree.lean), in the tree's order and nesting, each over its box, so a
// screen reader reads the page and its cursor is where the content is drawn.
//
// The engine decides what an element says: its `web.role`, its `web.aria` attributes and its
// `web.text`. This module writes them and nothing else: `role`, `tabindex`, `aria-` + a name of
// lower-case letters, text as text, and a box. It draws nothing (the elements are transparent and
// take no pointer events) and holds no page logic. An element is kept by its node id across
// trees, so a screen reader's position survives an update.

const NAME=/^[a-z]+$/;

/** The mirror in `root` (an empty element above the canvas). `onPress(x, y)` is called with the
 * centre of an element's box, in frame pixels of the window, when a screen reader activates it. */
export function createMirror(root,onPress){
  const doc=root.ownerDocument,elements=new Map();
  let view={top:0,scroll:0,ratio:1};
  const place=(el)=>{
    const box=el.axBox,style=el.style;
    if(!box||el.axText){style.position='';return;}
    style.position='fixed';
    style.left=`${box[0]/view.ratio}px`;style.top=`${(el.axFixed?box[1]:box[1]-view.scroll+view.top)/view.ratio}px`;
    style.width=`${box[2]/view.ratio}px`;style.height=`${box[3]/view.ratio}px`;
  };
  const write=(el,node)=>{
    const web=node.web??{},want=new Map();
    if(typeof web.role==='string'&&web.role)want.set('role',web.role);
    for(const [name,value] of Object.entries(web.aria??{}))
      if(NAME.test(name)&&typeof value==='string')want.set(`aria-${name}`,value);
    if(node.focusable)want.set('tabindex','-1');
    for(const name of el.axNames??[])if(!want.has(name))el.removeAttribute(name);
    for(const [name,value] of want)if(el.getAttribute(name)!==value)el.setAttribute(name,value);
    el.axNames=[...want.keys()];
    // The element's own text (a text node of the page, the value of a text field): its first child.
    const text=typeof web.text==='string'?web.text:undefined;
    if(text===undefined){if(el.axOwn){el.axOwn.remove();el.axOwn=undefined;}}
    else if(!el.axOwn){el.axOwn=doc.createTextNode(text);el.insertBefore(el.axOwn,el.firstChild);}
    else if(el.axOwn.data!==text)el.axOwn.data=text;
    el.axFixed=node.fixed===true; // of the chrome: window pixels, no scroll
    el.axBox=Array.isArray(node.box)&&node.box.length===4&&node.box.every(Number.isFinite)?node.box:undefined;
    place(el);
  };
  root.addEventListener('click',event=>{
    // A screen reader's activation: a click at the centre of the nearest element with a box.
    let el=event.target;
    while(el&&el!==root&&!el.axBox)el=el.parentNode;
    if(!el||el===root)return;
    const [x,y,w,h]=el.axBox;
    onPress(Math.floor(x+w/2),Math.floor((el.axFixed?y:y-view.scroll+view.top)+h/2));
  });
  return {
    /** The tree of an `accessibilityTree` answer; `ratio` is frame pixels per CSS pixel. The number of elements. */
    apply(answer,ratio){
      view={top:Number(answer.top)||0,scroll:Number(answer.scroll)||0,ratio:ratio>0?ratio:1};
      const nodes=(Array.isArray(answer.nodes)?answer.nodes:[]).filter(node=>node&&typeof node==='object'&&Number.isInteger(node.id));
      // What is gone leaves first, so that what stays is already in its place.
      const kept=new Set(nodes.map(node=>node.id));
      for(const [id,el] of elements)if(!kept.has(id)){el.remove();elements.delete(id);}
      const seen=new Set(),path=[],last=new Map();
      for(const node of nodes){
        if(seen.has(node.id))continue;
        seen.add(node.id);
        const isText=node.role==='text';
        let el=elements.get(node.id);
        if(el&&el.axText!==isText){el.remove();el=undefined;}
        if(!el){el=doc.createElement(isText?'span':'div');el.axText=isText;el.axId=node.id;elements.set(node.id,el);}
        const depth=Math.min(Math.max(0,Number.isInteger(node.depth)?node.depth:0),path.length);
        path.length=depth;
        const parent=path[depth-1]??root;
        // Its place among its parent's children: after the one placed before it (or the parent's own text).
        const before=last.get(parent)??parent.axOwn??null;
        const next=before?before.nextSibling:parent.firstChild;
        if(el.parentNode!==parent||next!==el)parent.insertBefore(el,next);
        last.set(parent,el);
        write(el,node);
        path.push(el);
      }
      return elements.size;
    },
    /** The page moved in the window (a scroll, a folded chrome, a zoom of the host) with the same tree. */
    move(top,scroll,ratio){
      view={top:Number(top)||0,scroll:Number(scroll)||0,ratio:ratio>0?ratio:view.ratio};
      for(const el of elements.values())place(el);
    },
    /** No page: no elements. */
    clear(){for(const el of elements.values())el.remove();elements.clear();},
    get size(){return elements.size;},
  };
}
