// Finding the newest Foafnaut build of the main branch among the releases of danbri/factoidal-builds.
// Shared by the foafnaut launcher (@factoidal/core, bin/foafnaut-releases.mjs) and Textnaut's native
// installer (@foafos/textnaut, lib/releases.mjs). The two files are identical; a test checks it.
//
// Why not just the release list: GitHub lists releases in no useful order, and with several release
// sets per build the newest macOS release can sit many pages in (2026-11-16: a first page of 60 missed
// build-0137191edfef and installed an older build). Why not just published_at: a branch build can be
// published after a main build, and a rebuild of an old commit is published late. So: read every page
// GitHub serves (the first 1000 releases, 10 pages), take the most recently published candidates, and
// ask the source repository which of them are on main and how far each is from main's head. The one nearest the head is the newest.

export const BUILDS = 'danbri/factoidal-builds';
export const CORE = 'danbri/factoidal-core';
const API = 'https://api.github.com';

/** The pointer the macOS release lane keeps (schema darwin-status/1). HEAD is the default branch. */
export const pointerUrl = (builds = BUILDS) => `https://raw.githubusercontent.com/${builds}/HEAD/latest/darwin-status.json`;
/** A release file's download URL; it follows from the tag, so no asset list is needed. */
export const assetUrl = (tag, name, builds = BUILDS) => `https://github.com/${builds}/releases/download/${tag}/${name}`;
export const tagPattern = (target) => new RegExp(`^build-([0-9a-f]{12})-foafnaut-${target}$`);

/** An error whose message is meant for the person at the terminal. */
export class ReleaseError extends Error {}

async function get(fetchImpl, url, headers) {
  try {
    return await fetchImpl(url, { headers, redirect: 'follow' });
  } catch (error) {
    throw new ReleaseError(`can not reach ${new URL(url).host} (${error.cause?.code ?? error.message}); check the network connection`);
  }
}

function apiError(reply, what) {
  const limited = (reply.status === 403 || reply.status === 429) && reply.headers?.get?.('x-ratelimit-remaining') === '0';
  if (limited) return new ReleaseError(`GitHub's API limit for this address is used up (${what}); try again within the hour, or set GITHUB_TOKEN`);
  return new ReleaseError(`${what}: HTTP ${reply.status} from GitHub`);
}

/** The page numbers named by a Link header: { next, last }. */
export function linkPages(link) {
  const out = {};
  for (const part of (link ?? '').split(',')) {
    const m = /<([^>]*)>\s*;\s*rel="(\w+)"/.exec(part);
    const page = m && new URL(m[1]).searchParams.get('page');
    if (page) out[m[2]] = Number(page);
  }
  return out;
}

/**
 * The releases of `builds`, reading at most maxPages pages of 100. Page 1 names the last page, and the
 * others are read together. GitHub serves only the first 1000 results of a list (a later page is refused
 * with HTTP 422; found 2026-11-17 when the list passed 10 pages), so maxPages is 10, and a later page that
 * fails is left out with a note in `skipped` rather than failing the whole list.
 */
export async function listReleases({ builds = BUILDS, fetchImpl = globalThis.fetch, headers, maxPages = 10, skipped = [] } = {}) {
  const page = async (n) => {
    const reply = await get(fetchImpl, `${API}/repos/${builds}/releases?per_page=100&page=${n}`, headers);
    if (!reply.ok) throw apiError(reply, `the release list of ${builds}`);
    return { list: await reply.json(), link: linkPages(reply.headers?.get?.('link')) };
  };
  const first = await page(1);
  const all = [...first.list];
  if (first.link.last) {
    const last = Math.min(first.link.last, maxPages);
    const rest = await Promise.allSettled(Array.from({ length: Math.max(0, last - 1) }, (_, i) => page(i + 2)));
    rest.forEach((r, i) => { if (r.status === 'fulfilled') all.push(...r.value.list); else skipped.push(`release list page ${i + 2}: ${r.reason.message}`); });
  } else {
    // No last link: follow next links one by one, within the same bound.
    for (let n = first.link.next, k = 1; n && k < maxPages; k++) {
      let r;
      try { r = await page(n); } catch (error) { skipped.push(`release list page ${n}: ${error.message}`); break; }
      all.push(...r.list);
      n = r.link.next;
    }
  }
  return all;
}

/** The macOS lane's pointer, as a candidate {tag, sha12, publishedAt}, or undefined. Never throws. */
export async function readPointer({ builds = BUILDS, fetchImpl = globalThis.fetch, target = 'darwin-arm64' } = {}) {
  if (target !== 'darwin-arm64') return undefined;
  try {
    const reply = await fetchImpl(pointerUrl(builds), { headers: { 'user-agent': 'foafnaut' }, redirect: 'follow' });
    if (!reply.ok) return undefined;
    const status = await reply.json();
    const r = status?.newest_release ?? status?.mac_release;
    const m = typeof r?.tag === 'string' && tagPattern(target).exec(r.tag);
    return m ? { tag: r.tag, sha12: m[1], publishedAt: r.published_at ?? '', fromPointer: true } : undefined;
  } catch {
    return undefined;
  }
}

/**
 * Where `sha` stands against `branch` of `core`: {onBranch, aheadBy, commit, committedAt}, where aheadBy
 * is the number of commits the branch has that `sha` does not (0 = the head). Undefined when unknown.
 */
async function position(fetchImpl, headers, core, sha, branch) {
  const reply = await get(fetchImpl, `${API}/repos/${core}/compare/${sha}...${branch}`, headers);
  if (reply.status === 404) return { onBranch: false };
  if (!reply.ok) throw apiError(reply, `comparing ${sha} with ${branch}`);
  const c = await reply.json();
  return { onBranch: c.behind_by === 0 && (c.status === 'ahead' || c.status === 'identical'), aheadBy: c.ahead_by,
    commit: c.base_commit?.sha, committedAt: c.base_commit?.commit?.committer?.date };
}

/**
 * The builds of `branch` that have a release for `target`, newest first:
 * [{tag, sha12, commit, committedAt, publishedAt, aheadBy}], plus `current` (where `currentSha` stands,
 * when given) and `notes` (what was skipped, for --verbose). Branch builds and builds of commits not on
 * `branch` are left out. Only the `maxCompare` most recently published candidates are checked.
 */
export async function mainReleases({ target = 'darwin-arm64', builds = BUILDS, core = CORE, branch = 'main', currentSha,
  fetchImpl = globalThis.fetch, env = process.env, maxPages = 10, maxCompare = 8 } = {}) {
  const token = env.GITHUB_TOKEN || env.GH_TOKEN;
  const headers = { accept: 'application/vnd.github+json', 'user-agent': 'foafnaut', ...(token ? { authorization: `Bearer ${token}` } : {}) };
  const pattern = tagPattern(target);
  const notes = [];
  const [pointer, listing] = await Promise.all([
    readPointer({ builds, fetchImpl, target }),
    listReleases({ builds, fetchImpl, headers, maxPages, skipped: notes }).then((list) => ({ list }), (error) => ({ error })),
  ]);
  const byTag = new Map();
  for (const r of listing.list ?? []) {
    const m = pattern.exec(r.tag_name ?? '');
    if (m && r.published_at && !r.draft) byTag.set(r.tag_name, { tag: r.tag_name, sha12: m[1], publishedAt: r.published_at });
  }
  if (listing.error) {
    if (!pointer) throw listing.error;
    notes.push(`${listing.error.message}; using the macOS lane's pointer alone`);
  }
  const candidates = [...byTag.values()].sort((a, b) => b.publishedAt.localeCompare(a.publishedAt)).slice(0, maxCompare);
  if (pointer && !candidates.some((c) => c.tag === pointer.tag)) candidates.push(byTag.get(pointer.tag) ?? pointer);
  if (candidates.length === 0) return { releases: [], current: undefined, notes };
  const shas = [...new Set([...candidates.map((c) => c.sha12), ...(currentSha ? [currentSha] : [])])];
  const settled = await Promise.allSettled(shas.map((s) => position(fetchImpl, headers, core, s, branch)));
  const where = new Map(shas.map((s, i) => [s, settled[i]]));
  const failures = settled.filter((s) => s.status === 'rejected');
  if (failures.length === shas.length) {
    // Nothing could be checked against main. The lane's pointer only ever names a main build.
    if (!pointer) throw failures[0].reason;
    notes.push(`${failures[0].reason.message}; using the macOS lane's pointer unchecked`);
    return { releases: [{ ...pointer, commit: undefined, committedAt: undefined, aheadBy: undefined }], current: undefined, notes };
  }
  const releases = [];
  for (const c of candidates) {
    const p = where.get(c.sha12);
    if (p.status === 'rejected') { notes.push(`${c.tag}: ${p.reason.message}`); continue; }
    if (!p.value.onBranch) { notes.push(`${c.tag}: not on ${branch} (a branch build); skipped`); continue; }
    releases.push({ tag: c.tag, sha12: c.sha12, commit: p.value.commit, committedAt: p.value.committedAt, publishedAt: c.publishedAt, aheadBy: p.value.aheadBy });
  }
  releases.sort((a, b) => a.aheadBy - b.aheadBy || b.publishedAt.localeCompare(a.publishedAt));
  const cur = currentSha && where.get(currentSha);
  return { releases, current: cur?.status === 'fulfilled' ? cur.value : undefined, notes };
}
