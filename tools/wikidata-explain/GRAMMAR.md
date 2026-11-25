# An abstract grammar of set browsing

`src/grammar.mjs` turns a parsed query into a **program**: chains of set
browsing, held together by **combine** nodes for what browsing cannot do.
The program is data only. It holds variables, SPARQL terms and the SPARQL each
step stands for, and no wording. The words are kept in a separate **lexicon**,
keyed by those same terms. Views can therefore change freely without touching
the data:

- the block page (`docs/web/hub/wikidata-parallax/`);
- a bead chain, as in kgx/daisychain;
- a node DAG, as in kgx/pivcab;
- a plain-English reading.

```
grammarOf(query, nameOf) -> { program, steps, prefixes, vars, lex }
```

## Program

```
Program  = { parts: (Chain | Combine)[], where: Sparql[] }

Chain    = { t:'chain', rows: Step[][] }           row 0 is the spine; later
                                                   rows branch off a set
Step     = Set | Pivot | From

Set      = { t:'set', v, type, values, narrow, keep, show, sparql, any?, step? }
  v        the variable ("painting")
  type     "wd:Q3305213" when the set is "every <type>", else null
  values   ["wd:Q43459", …] when the query names its items (VALUES), else null
  narrow   [{ p, inv, opt, any?, o: [term…], sparql }]   facets: p = o
  keep     [{ mode: exclude|require|anyOf, key, sparql }]  chips
  show     [{ p, inv, opt, any?, v, sparql }]            columns
  sparql   the set's own fragments (type triple, VALUES)

Pivot    = { t:'pivot', p, inv, opt, any?, sparql, step? }
  p        the property as SPARQL: an IRI ("wdt:P50"), a path
           ("wdt:P31/wdt:P279*"), or a variable ("?p") for any property
  inv      true: "things with them as p"; false: "their p"

From     = { t:'from', v }                         a branch row starts here

Combine  = { t:'combine', op, args: Program[], on?, out?, why?, sparql, step? }
  op = join      separate chains, matched on `on` (conditions), or every combination
       either    OR whose branches are whole patterns (one arg per branch)
       except    exclusion that is not a single facet; `on` = shared variables
       optional  a nested "where present" part
       stage     a subquery worked out on its own; `out` = what it passes on
       link      an extra edge that closes a cycle
  why      the classifier's blocker code (plain words are in lex[why])
```

`where` holds the program's remaining filters and computed values, as SPARQL
(`FILTER(…)`, `BIND(… AS ?x)`).

## Lexicon

`lex` maps keys to display text:

| key | example | text |
|---|---|---|
| `?var` | `?alum` | `alum` |
| property SPARQL | `wdt:P27` | `country of citizenship (P27)` |
| value term | `wd:Q145` | `United Kingdom (Q145)` |
| condition SPARQL | `BIND(LANG(?label) AS ?langcode)` | `?langcode = the language tag of ?label` |
| blocker code | `negation tied to two columns: …` | `What it leaves out depends on two values at once…` |
| chip key | `MINUS { … }` | `country of citizenship includes United Kingdom` |

Another language, or another register (expert, child, screen reader), is a
different lexicon over the same program.

## Steps

`steps` lists the order in which a stepper adds parts of the query, matching
the `step` numbers on the program's nodes:

- every Set and Pivot of a top-level chain;
- each Combine as a whole (a join's chains are walked first, since a join is
  plain conjunction);
- then the where-list.

```
Step = { kind, v, sparql: [{ s, at }] }
  v    the set the step lands on (a pivot lands on the set it leads to)
  s    a SPARQL fragment;  at  its offset in the whole query, so a draft
       keeps the query's own order (VALUES first, BIND before its users)
```

`draft.mjs` (`docs/web/hub/wikidata-parallax/`) builds the draft for step k:
every fragment of steps 0..k, deduplicated and in query order. It gives
either a sample of rows, or a count of distinct items on the landing set.

Every draft of all 536 queries parses with sparqljs. All 536 whole queries
round-trip through `sparql.mjs`. The page's last step is the whole query, as
rewritten for QLever.

## What the rows carry, and the answer's shape

After a pivot, the rows are pairs, not a set. "Alumni, then their nationality" gives one row per
(alum, nationality): 317 rows over 96 nationalities, reached from 285 alumni. Three
readings of the same step:

| reading | what | in SPARQL |
|---|---|---|
| set | each nationality once (Parallax's view) | `SELECT DISTINCT ?nationality` |
| bag | a nationality once per alum who has it | `SELECT ?nationality` |
| rows | (alum, nationality) pairs: each keeps its trail back | `SELECT ?alum ?nationality` |

The grammar records:

- `steps[k].carries`: the sets the rows hold after step k (`["alum", "nationality"]`).
- `answer = { shape, vars, counted, aggregates, distinct, order }`: what the query makes
  of the rows. `shape` is `rows` (it returns two or more of the sets), `set` (one, `DISTINCT`),
  `bag` (one, with repeats) or `counted` (it groups and counts).
- On a Set reached from earlier sets, `shape` and `with`: which earlier sets the answer keeps
  beside it ("with their ?alum"), or which it is repeated or counted per.

A step's count asks, in one request, for the distinct items of the set it lands on, the distinct
items of each earlier set it carries, and the rows. "Top values" groups the landing set to show it
as a bag: each item with the number of rows that reach it. That number is daisychain's
`originCount`.

## How it maps onto the kgx demos

| grammar | daisychain | pivcab |
|---|---|---|
| Set | a data bead (a Bundle) | a Source or Snapshot node |
| narrow / keep | a filter op chip on the frontier bead | a Filter node |
| Pivot | a pivot op (a relation template's default variant) | an edge to a new node |
| show | enrich (grows each item's mini-graph) | (tile fields) |
| Chain | the bead spine | a path in the DAG |
| combine either / join / except | the Bundle's union / intersect / difference | the Combine bar (two picked nodes) |
| combine stage | (none: a grouped sub-bead) | (none) |
| steps 0..k | "tap an earlier bead": truncate back to it | selecting a node shows its bundle |
| lex | chip and bead labels | node labels |

Two daisychain ideas fit the grammar directly:

- **Relation templates:** a Pivot's `p` can be one variant of a named
  relation, with `tighten` and `broaden` alternatives. A view could then
  offer "broaden this pivot" with no change to the data model.
- **Provenance:** each step's `sparql` already says which part of the query a
  set came from. Daisychain's named graph per source is the same idea at run
  time.
