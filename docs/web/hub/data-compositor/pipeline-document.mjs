// Application documents describe a fixed, versioned recipe and its editable
// inputs/layout. They never import JavaScript, credentials or runtime evidence.
export const MAX_PIPELINE_BYTES = 2 * 1024 * 1024;
export const RECIPES = Object.freeze({
  'rdf-to-html': { inputs: ['turtle','csv','metadata','query','stylesheet','minScore'], nodes: ['turtle','csvw','merge','closure','graphs','query','filter','xml','xslt','diagnostic','report','html'] },
  'xml-signature': { inputs: ['source','stylesheet','mode'], nodes: [] },
});
const fail = message => { throw new TypeError(`Pipeline document: ${message}`); };
function record(value, name) {
  if (!value || typeof value !== 'object' || Array.isArray(value) || Object.getPrototypeOf(value) !== Object.prototype) fail(`${name} must be an object`);
}
function keys(value, allowed, name) {
  record(value,name);
  for (const key of Object.keys(value)) if (!allowed.includes(key)) fail(`unknown ${name} field ${key}`);
}
export function validatePipelineDocument(value, expectedRecipe) {
  keys(value,['format','version','recipe','title','inputs','layout','view'],'top-level');
  if (value.format !== 'factoidal-compositor' || value.version !== 1) fail('unsupported format or version');
  if (!Object.hasOwn(RECIPES,value.recipe)) fail('unknown recipe');
  if (expectedRecipe && value.recipe !== expectedRecipe) fail(`open this file in the ${value.recipe} compositor`);
  if (typeof value.title !== 'string' || !value.title.trim() || value.title.length > 160) fail('title must have 1–160 characters');
  const spec=RECIPES[value.recipe]; keys(value.inputs,spec.inputs,'input');
  const inputs={};
  for (const key of spec.inputs) {
    if (typeof value.inputs[key] !== 'string') fail(`input ${key} must be text`);
    inputs[key]=value.inputs[key];
  }
  if (value.recipe === 'rdf-to-html') {
    const n=Number(inputs.minScore);
    if (!inputs.minScore.trim() || !Number.isFinite(n) || n<0 || n>100) fail('minimum score must be 0–100');
  } else if (!['original','preprocessed','embedded-xslt'].includes(inputs.mode)) fail('unknown signature example');
  const layout=[];
  if (value.layout !== undefined) {
    if (!Array.isArray(value.layout) || value.layout.length > spec.nodes.length) fail('invalid node layout');
    const seen=new Set();
    for (const node of value.layout) {
      keys(node,['id','x','y'],'layout');
      if (!spec.nodes.includes(node.id) || seen.has(node.id)) fail('unknown or repeated layout node');
      if (![node.x,node.y].every(n=>typeof n==='number'&&Number.isFinite(n)&&n>=0&&n<=10000)) fail('invalid node coordinates');
      seen.add(node.id); layout.push({id:node.id,x:node.x,y:node.y});
    }
  }
  const view={evidence:false};
  if (value.view !== undefined) {
    keys(value.view,['evidence'],'view');
    if (typeof value.view.evidence !== 'boolean') fail('evidence setting must be boolean');
    view.evidence=value.view.evidence;
  }
  return {format:'factoidal-compositor',version:1,recipe:value.recipe,title:value.title.trim(),inputs,layout,view};
}
export function decodePipelineDocument(text,expectedRecipe) {
  if (typeof text !== 'string' || new TextEncoder().encode(text).length > MAX_PIPELINE_BYTES) fail('file exceeds 2 MiB');
  return validatePipelineDocument(JSON.parse(text),expectedRecipe);
}
export function encodePipelineDocument(value,expectedRecipe) {
  const text=JSON.stringify(validatePipelineDocument(value,expectedRecipe),null,2)+'\n';
  if (new TextEncoder().encode(text).length > MAX_PIPELINE_BYTES) fail('file exceeds 2 MiB');
  return text;
}
export function pipelineSnapshot(recipe,title,inputs,layout=[],view={evidence:false}) {
  const spec=RECIPES[recipe]; if (!spec) fail('unknown recipe');
  // Capture only editable fields, never the component's other live state.
  return validatePipelineDocument({format:'factoidal-compositor',version:1,recipe,title,
    inputs:Object.fromEntries(spec.inputs.map(key=>[key,inputs[key]])),layout,view},recipe);
}
