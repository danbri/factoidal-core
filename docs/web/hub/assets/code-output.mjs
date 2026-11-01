// Display-only controls. Original text is never parsed, normalized or reformatted.
let highlighter;
const views = new WeakMap();
const aliases = { 'observable-js':'javascript', js:'javascript', ts:'typescript', ttl:'turtle', sh:'bash' };
const loadHighlight = () => highlighter ??= import('../../../vendor/shiki/highlight.mjs');
function innerCode(html) { return html.slice(html.indexOf('<code>') + 6, html.lastIndexOf('</code>')); }
function button(text, action) { const el=document.createElement('button'); el.type='button'; el.textContent=text; el.addEventListener('click',action); return el; }
export function codeControls(pre, code, {original, formattedText, language='text'}={}) {
  const controls=document.createElement('div'); controls.className='code-output-controls';
  let formatted=false;
  const getOriginal=()=>original===undefined?code.textContent:original;
  const copy=button('Copy',async()=>{
    try { await navigator.clipboard.writeText(getOriginal()); copy.textContent='Copied'; }
    catch { copy.textContent='Copy unavailable'; }
  });
  copy.title='Copy the original text, without display changes';
  const wrap=button('Wrap',()=>{ const on=pre.classList.toggle('code-wrap'); wrap.setAttribute('aria-pressed',String(on)); });
  wrap.setAttribute('aria-pressed','false'); controls.append(copy,wrap);
  const show=async text=>{
    code.textContent=text;
    try {
      const {highlight}=await loadHighlight();
      const html=innerCode(highlight(text,aliases[language]||language));
      // Only install spans if they preserve the exact displayed string.
      const probe=document.createElement('code');probe.innerHTML=html;
      if(code.textContent===text && probe.textContent===text)code.innerHTML=html;
    } catch { /* Plain text remains usable offline if an asset is missing. */ }
  };
  if(typeof formattedText==='string') {
    const toggle=button('Formatted',()=>{ formatted=!formatted;toggle.textContent=formatted?'Raw':'Formatted';toggle.setAttribute('aria-pressed',String(formatted));void show(formatted?formattedText:getOriginal()); });
    toggle.title='Display the caller-supplied formatted representation; Copy keeps the original';toggle.setAttribute('aria-pressed','false');controls.append(toggle);
  }
  return { controls, highlight:()=>show(getOriginal()) };
}
export class CodeOutput extends (globalThis.HTMLElement??class {}) {
  setValue(text,{language='text',formattedText}={}) {
    if(typeof text!=='string')throw new TypeError('CodeOutput text must be a string');
    if(formattedText!==undefined&&typeof formattedText!=='string')throw new TypeError('formattedText must be a string');
    this.replaceChildren();this.classList.add('code-output');
    const pre=document.createElement('pre'),code=document.createElement('code');pre.tabIndex=0;code.textContent=text;code.className='shiki-code';pre.append(code);
    const view=codeControls(pre,code,{original:text,language,formattedText});this.append(view.controls,pre);return view.highlight();
  }
}
if(globalThis.customElements&&!customElements.get('factoidal-code-output'))customElements.define('factoidal-code-output',CodeOutput);
export function enhanceCodeBlocks(root=document) {
  // Preserve the original pre>code, classes, flags and executable textContent.
  for(const code of root.querySelectorAll('pre > code')) {
    const pre=code.parentElement;
    if(pre.closest('factoidal-code-output'))continue;
    if(pre.dataset.codeControls){if(!code.querySelector('span'))void views.get(pre)?.highlight();continue;}
    pre.dataset.codeControls='true';code.classList.add('shiki-code');
    const language=[...code.classList].find(c=>c.startsWith('language-'))?.slice(9)||'text';
    const view=codeControls(pre,code,{language});views.set(pre,view);pre.before(view.controls);
    // Static fences already have spans. Avoid loading the bundle twice.
    if(!code.querySelector('span'))void view.highlight();
  }
}
