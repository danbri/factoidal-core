// Drive our LWS client through one Touchstone client-lab session
// (https://github.com/ebremer/touchstone, harness-clients) and judge the
// result. https://github.com/danbri/factoidal/issues/917
//
//   node tests/lws/client/touchstone-session.mjs BASE OUTDIR
//
// BASE is the lab's public base (for example
// http://localhost:18090/touchstone/clients). Run by
// tools/lws-touchstone-client.sh, which builds and starts the lab.
//
// This file is the developer of CLIENT-TESTING.md: it starts a session,
// starts the tasks of the rules that need one (POST .../tasks/{rule}), and
// asks OUR client (npm/factoidal/lws/client.mjs, every decision in
// formal/lean4/L4Factoidal/LWS/Client/) to do what each task says. It uses
// the session API for what a developer does by hand (a SAML assertion as
// the subject token, the tasks, the results). Every request to the storage,
// the authorization server and the inbox is our client's.
//
// Outcomes: passed, failed, cantTell, untested, inapplicable. The rows of
// tests/lws/client/touchstone-xfail.tsv are rules expected NOT to pass, each
// with its open issue. Exit 0 when the session ran, no rule failed, and every
// rule that did not pass is listed there; 1 when a rule failed, a rule that
// is not listed did not pass, or a listed rule passed (flip it to a real
// expectation and close the issue); 2 when the session could not run.

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs'
import { fileURLToPath } from 'node:url'

const [base, outDir] = process.argv.slice(2)
if (!base || !outDir) {
  console.error('usage: node tests/lws/client/touchstone-session.mjs BASE OUTDIR')
  process.exit(2)
}
mkdirSync(outDir, { recursive: true })

const SAML2 = 'urn:ietf:params:oauth:token-type:saml2'
const steps = []
const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms))

async function step (name, body) {
  try {
    const r = await body()
    steps.push(`ok    ${name}`)
    return r
  } catch (error) {
    const why = error && error.reason ? `${error.reason} ${JSON.stringify(error.detail)}` : String(error && error.message)
    steps.push(`fail  ${name}: ${why}`)
    return undefined
  }
}

/** A step whose operation is expected to end with this failure code. */
async function expectFail (name, reason, body) {
  try {
    await body()
    steps.push(`fail  ${name}: it did not fail (expected ${reason})`)
  } catch (error) {
    if (error && error.reason === reason) steps.push(`ok    ${name} (ended with ${reason})`)
    else steps.push(`fail  ${name}: ended with ${error && error.reason} ${JSON.stringify(error && error.detail)}`)
  }
}

async function main () {
  const { loadEngine } = await import('../../../npm/factoidal/bin/engine.mjs')
  const { createLwsClient, createNotificationReceiver, lwsClientOpsAvailable } =
    await import('../../../npm/factoidal/lws/client.mjs')
  const engine = await loadEngine()
  const probe = await lwsClientOpsAvailable(engine)
  if (!probe.available) {
    console.error(`touchstone-session: CANNOT RUN: ${probe.reason}`)
    return 2
  }
  const pkg = JSON.parse(readFileSync(fileURLToPath(new URL('../../../npm/factoidal/package.json', import.meta.url)), 'utf8'))

  // The session (the lab's API, as a developer's CI uses it).
  const created = await fetch(`${base}/sessions`, {
    method: 'POST',
    headers: { 'content-type': 'application/json' },
    body: JSON.stringify({
      clientUnderTest: { name: 'Factoidal LWS client', version: pkg.version, homepage: 'https://github.com/danbri/factoidal' },
      areas: ['core', 'authentication', 'notifications', 'index']
    })
  })
  if (created.status !== 201) {
    console.error(`touchstone-session: CANNOT RUN: POST /sessions answered ${created.status} ${await created.text()}`)
    return 2
  }
  const session = await created.json()
  const api = session.api
  const key = { authorization: `Bearer ${session.key}` }
  const task = async (rule) => {
    const r = await fetch(`${api}/tasks/${rule}`, { method: 'POST', headers: key })
    await r.arrayBuffer()
    if (r.status !== 204) throw new Error(`task ${rule} answered ${r.status}`)
  }
  const assertion = await (await fetch(`${api}/assertions/alice`, { method: 'POST', headers: key })).json()
  const bobWebId = session.identities.bob.webid
  const storage = session.storage
  console.log(`touchstone-session: session ${session.id}, storage ${storage}`)

  const client = await createLwsClient({ engine, subjectToken: assertion.assertion, subjectTokenType: SAML2 })
  const receiver = await createNotificationReceiver({ client })
  const waitDeliveries = async (n) => {
    for (let i = 0; i < 100 && receiver.received().length < n; i += 1) await sleep(100)
  }

  try {
    const desc = await step('discover the storage', () => client.discover(storage))
    const root = await step('list the storage root', () => client.list(storage))
    await task('client-create-container-type-link')
    const notes = (await step('create a container', () => client.create(storage, { container: true, slug: 'notes' })) || {}).location
    const note = (await step('create a data resource', () =>
      client.create(notes, { slug: 'note.txt', mediaType: 'text/plain', body: 'milk' })) || {}).location
    await step('update it, conditional on its ETag', () => client.update(note, { mediaType: 'text/plain', body: 'milk eggs' }))
    const ls = await step('read its linkset', () => client.readLinkset(note))
    await step('patch its linkset, conditional, in an advertised format', () => client.updateLinkset(note, {
      body: JSON.stringify([{ op: 'add', path: '/linkset/0/https:~1~1example.org~1tag', value: [{ href: 'https://example.org/t1' }] }])
    }))
    await task('client-no-repeat-after-405-415')
    await expectFail('replace its linkset with PUT; the lab refuses once with 405', 'methodRefused', () =>
      client.updateLinkset(note, { mediaType: 'application/linkset+json', body: JSON.stringify((ls && ls.linkset) || { linkset: [] }) }))
    await task('client-combined-update-prefer-set-linkset')
    await step('update content and metadata in one request', () => client.update(note, {
      mediaType: 'text/plain', body: 'milk eggs bread', links: ['<https://example.org/ShoppingList>; rel="type"']
    }))
    await task('client-no-blind-retry-of-create')
    await expectFail('create; the lab creates it and answers 503', 'createOutcomeUnknown', () =>
      client.create(notes, { slug: 'lost.txt', mediaType: 'text/plain', body: 'lost' }))

    // Pagination: more members than a page holds.
    const many = (await step('create a container for paging', () => client.create(storage, { container: true, slug: 'many' })) || {}).location
    for (let i = 0; i < 12; i += 1) {
      await step(`create member ${i} with a type`, () => client.create(many, {
        slug: `m${i}.txt`, mediaType: 'text/plain', body: String(i), types: ['https://example.org/Recipe']
      }))
    }
    const listed = await step('list every page of the container', () => client.list(many))
    if (listed) steps.push(`info  listing: ${listed.items.length} items over ${listed.pages} pages`)

    await task('client-delete-container-depth')
    const tmp = (await step('create a container to delete', () => client.create(storage, { container: true, slug: 'tmp' })) || {}).location
    await step('put a member in it', () => client.create(tmp, { slug: 'x.txt', mediaType: 'text/plain', body: 'x' }))
    await step('delete it with everything in it, conditional on its ETag', () =>
      client.delete(tmp, { recursive: true, precondition: 'ifMatchCurrent' }))
    const d1 = (await step('create a resource to delete', () => client.create(notes, { slug: 'd.txt', mediaType: 'text/plain', body: 'd' })) || {}).location
    await step('delete it, conditional on its ETag', () => client.delete(d1, { precondition: 'ifMatchCurrent' }))

    // Index: the lab shows a write after three seconds (lws10-index: no
    // read-your-writes).
    await sleep(3500)
    await step('read the type index', () => client.typeIndex(storage))
    await step('search by type', () => client.search(storage, { query: { type: ['https://example.org/Recipe'] } }))
    await step('search in another query format first, then the baseline after its 415', () => client.search(storage, {
      mediaType: 'application/sparql-query', body: 'SELECT ?s WHERE { ?s a <https://example.org/Recipe> }',
      query: { type: ['https://example.org/Recipe'] }
    }))
    await task('client-restart-after-refused-page')
    await step('search again; the lab refuses the next page once with 410', () =>
      client.search(storage, { query: { type: ['https://example.org/Recipe'] } }))

    // Notifications.
    const sub = await step('subscribe with a webhook', () => client.subscribe(note, { inbox: `${receiver.url}inbox/1` }))
    await step('subscribe again with another inbox', () => client.subscribe(note, { inbox: `${receiver.url}inbox/2` }))
    let expected = 0
    await step('change the resource (a genuine notification)', () => client.update(note, { mediaType: 'text/plain', body: 'v1' }))
    expected += 2
    await waitDeliveries(expected)
    for (const rule of ['client-inbox-refuses-unpublished-key', 'client-inbox-refuses-altered-body',
      'client-inbox-refuses-keyid-without-fragment', 'client-inbox-refuses-foreign-key-document']) {
      await task(rule)
      await step(`change the resource (${rule})`, () => client.update(note, { mediaType: 'text/plain', body: rule }))
      expected += 2
      await waitDeliveries(expected)
    }
    const verdicts = receiver.received()
    steps.push(`info  the receiver answered ${verdicts.length} deliveries: ${verdicts.filter((v) => v.accept).length} accepted, ` +
      `${verdicts.filter((v) => !v.accept).length} refused (${[...new Set(verdicts.filter((v) => !v.accept).map((v) => v.reason))].join('; ')})`)
    const third = await step('subscribe a third time', () => client.subscribe(note, { inbox: `${receiver.url}inbox/4` }))
    if (third && third.location) await step('unsubscribe', () => client.unsubscribe(third.location))
    if (sub) steps.push(`info  first subscription: ${sub.location}`)

    // Access requests and grants.
    await step('request access', () => client.requestAccess(storage, {
      actions: ['read'], assignee: bobWebId, targets: [note], inbox: `${receiver.url}inbox/3`
    }))
    const grant = await step('grant access', () => client.grantAccess(storage, {
      actions: ['read', 'modify'], assignee: bobWebId, targets: [note],
      constraint: [{ leftOperand: 'dateTime', operator: 'lt', rightOperand: '2099-01-01T00:00:00Z' }]
    }))
    if (grant && grant.location) {
      await step('read the grant', () => client.getAccess(grant.location))
      await step('revoke the grant', () => client.revokeAccess(grant.location))
    }

    // Moving.
    if (desc) {
      const dest = (await step('create a destination container', () => client.create(storage, { container: true, slug: 'archive' })) || {}).location
      if (dest) await step('move the resource', () => client.move(note, { destination: dest }))
    }

    // The decoy, then a resource after the lab refuses our token once.
    await task('client-token-after-discovery-checks')
    const first = root && root.items.length > 0 ? root.items[0] : null
    if (first) {
      await expectFail('open the first entry of the root (the decoy)', 'discoveryValidation', () => client.read(first))
    } else {
      steps.push('fail  the root listing has no first entry')
    }
    await step('read a resource after the lab refuses the token once', () => client.read(notes))
  } finally {
    await receiver.close()
  }

  // Results.
  const results = await (await fetch(`${api}/results`, { headers: key })).json()
  writeFileSync(`${outDir}/results.json`, JSON.stringify(results, null, 2))
  writeFileSync(`${outDir}/earl.ttl`, await (await fetch(`${api}/results?format=earl`, { headers: key })).text())
  const xfail = new Map()
  const xfailPath = fileURLToPath(new URL('./touchstone-xfail.tsv', import.meta.url))
  for (const line of readFileSync(xfailPath, 'utf8').split('\n')) {
    if (line.trim() === '' || line.startsWith('#')) continue
    const [rule, issue] = line.split('\t')
    xfail.set(rule, issue)
  }
  for (const s of steps) console.log(`  ${s}`)
  const counts = { passed: 0, failed: 0, cantTell: 0, untested: 0, inapplicable: 0 }
  const problems = []
  for (const r of results.rules) {
    counts[r.outcome] = (counts[r.outcome] || 0) + 1
    const listed = xfail.get(r.rule)
    const mark = r.outcome === 'passed' ? (listed ? 'XPASS' : 'pass ')
      : (listed ? 'xfail' : (r.outcome === 'failed' ? 'FAIL ' : r.outcome.toUpperCase().slice(0, 5)))
    console.log(`  ${mark} ${r.level.padEnd(6)} ${r.rule} ${r.outcome}${listed ? ` (${listed})` : ''}`)
    if (r.outcome === 'failed') {
      problems.push(`${r.rule} failed: ${JSON.stringify(r.evidence).slice(0, 400)}`)
    } else if (r.outcome === 'passed' && listed) {
      problems.push(`${r.rule} passed but is listed as an expected failure (${listed}): flip it and close the issue`)
    } else if (r.outcome !== 'passed' && !listed) {
      problems.push(`${r.rule} is ${r.outcome} and is not listed as an expected failure`)
    }
  }
  for (const p of problems) console.log(`  PROBLEM ${p}`)
  const total = results.rules.length
  console.log(`touchstone client lab: ${counts.passed} pass, ${counts.failed} fail, ${counts.inapplicable} inapplicable, ` +
    `${counts.untested} untested, ${counts.cantTell} cantTell (out of ${total}); ` +
    `${[...xfail.keys()].length} expected failures listed; verdict: ${results.verdict.text}`)
  await fetch(api, { method: 'DELETE', headers: key })
  return problems.length === 0 ? 0 : 1
}

let rc = 2
try {
  rc = await main()
} catch (error) {
  console.error(`touchstone-session: CANNOT RUN: ${error && error.stack ? error.stack : error}`)
  rc = 2
}
process.exitCode = rc
