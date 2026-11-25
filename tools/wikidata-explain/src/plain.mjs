// Plain-English versions of the classifier's reasons, for readers who
// don't know SPARQL. The classifier's own wording stays as hover text.
const RULES = [
  [/^OR whose branches/, 'It chooses between whole patterns, not between values of one facet.'],
  [/^join on a computed value/, 'It matches up separate sets by a computed value, or not at all.'],
  [/^any property/, 'It follows any property at all, not a chosen one.'],
  [/^cyclic join/, 'Its links come back round in a loop, so it is not one path out from a starting set.'],
  [/^negation tied to two columns/, 'What it leaves out depends on two values at once, so no single facet can show it.'],
  [/^negated combination/, 'It leaves out items that match a combination of conditions, which no single facet can show.'],
  [/^negation of a complex property path/, 'It leaves out items reached by a complex path of properties.'],
  [/^negation over any property/, 'It leaves out items linked by any property at all.'],
  [/^negated chain of (\d+) hops/, 'It leaves out items by following a chain of $1 links, too long for one facet.'],
  [/^negation with a condition inside/, 'What it leaves out depends on a condition, not on one facet value.'],
  [/^negation with several conditions inside/, 'What it leaves out depends on several conditions together.'],
  [/^negation on a column that may be blank/, 'It leaves out items using a value that may be missing.'],
  [/^negation containing (\w+)/, 'It leaves out items using a pattern with $1 inside.'],
  [/^negation with no graph pattern/, 'It has an exclusion with nothing to match.'],
  [/^exclusion that removes nothing/, 'It has an exclusion that shares nothing with the results, so it removes nothing.'],
  [/^existence test unrelated/, 'It tests for something unrelated to the results.'],
  [/^existence test combined/, 'It combines a test for whether something exists with other conditions.'],
  [/^(optional|minus|union) inside OPTIONAL/, 'It has an optional part with its own $1 inside.'],
  [/^subquery that is not set browsing/, 'It works something out in a separate stage that is not browsing itself.'],
  [/^multi-column VALUES/, 'It starts from a fixed table of several columns.'],
  [/^external service/, 'It calls another query service.'],
  [/^property path with excluded properties/, 'It follows any property except some named ones.'],
  [/^no graph pattern/, 'It has no pattern to browse.'],
  [/^unsupported element: (\w+)/, 'It uses a construct ($1) that this view does not draw.'],
];
export function plainReason(code) {
  for (const [re, text] of RULES) {
    const m = re.exec(code);
    if (m) return text.replace(/\$(\d)/g, (_, i) => m[+i] === 'minus' ? 'exclusion' : m[+i] === 'union' ? 'OR' : m[+i]);
  }
  return code;
}
