#!/usr/bin/env python3
"""Forgotten-branch audit: every branch of a repository, classified, as a table.

    tools/branch-audit.py [--repo OWNER/NAME[=LOCAL_CLONE]] ... [--json] [--stale-days N]
                          [--patch-id] [--fetch] [--local-only | --remote-only]

Read-only towards the repositories: it changes no branch, PR or file in them. It reads
the branches of a local clone (`git for-each-ref`), and the pull requests with one
`gh pr list --state all` call per repository. `--fetch` runs `git fetch --prune origin`
in the clone first (that updates remote-tracking refs only). Without a LOCAL_CLONE, a
blob-less bare mirror is kept in ~/.cache/factoidal-branch-audit/ and fetched each run.

Each branch gets one class and one action:

  merged          its head is in the default branch            -> delete candidate
  merged-pr       a merged PR had exactly this head (squash)   -> delete candidate
  merged-patch    its whole diff equals a default-branch commit
                  (patch-id; only with --patch-id)              -> delete candidate
  merged-pr-later a PR merged, but the branch moved on after   -> review
  open-pr         open PR updated within --stale-days          -> none
  open-pr-stale   open PR not updated for --stale-days         -> ping
  closed-pr       its PR was closed unmerged                   -> review
  no-pr           unmerged, no PR                              -> review
  local-unpushed  local branch with commits not on its remote  -> push (wip/) or review
  local-only      local branch with no remote counterpart      -> push (wip/) or review

Default repositories: danbri/factoidal-core=<this checkout>. Skill:
skills/cleanup-and-recovery/SKILL.md section 4. Tests: tools/branch-audit-test.py.
"""
import argparse, datetime as dt, json, os, subprocess, sys

DELETE, REVIEW, PING, PUSH, NONE = 'delete candidate', 'review', 'ping', 'push or review', '-'


def run(args, cwd=None, check=True):
    p = subprocess.run(args, cwd=cwd, capture_output=True, text=True)
    if check and p.returncode != 0:
        raise RuntimeError(f"{' '.join(args)}: {p.stderr.strip()[:300]}")
    return p.stdout


def classify(b, prs, default_sha_has, now, stale_days, patch_equal=None):
    """Pure decision for one branch.

    b: {'name','sha','date' (datetime, UTC),'remote' (bool),'local' (bool),'unpushed' (int|None)}
    prs: PRs whose headRefName is b['name']: [{'number','state','headRefOid','updatedAt','mergedAt'}]
    default_sha_has: bool, the branch head is an ancestor of the default branch.
    patch_equal: True/False/None (None: not checked).
    Returns (class, action, pr_text).
    """
    if not b.get('remote'):
        if default_sha_has:
            return 'merged', DELETE, ''
        return 'local-only', PUSH, ''
    if default_sha_has:
        return 'merged', DELETE, _prtext(prs)
    if b.get('local') and (b.get('unpushed') or 0) > 0:
        return 'local-unpushed', PUSH, ''
    merged = [p for p in prs if p['state'] == 'MERGED']
    if any(p.get('headRefOid') == b['sha'] for p in merged):
        return 'merged-pr', DELETE, _prtext(merged)
    if patch_equal:
        return 'merged-patch', DELETE, _prtext(prs)
    open_ = [p for p in prs if p['state'] == 'OPEN']
    if open_:
        newest = max(_ts(p['updatedAt']) for p in open_)
        if (now - newest).days >= stale_days:
            return 'open-pr-stale', PING, _prtext(open_)
        return 'open-pr', NONE, _prtext(open_)
    if merged:
        return 'merged-pr-later', REVIEW, _prtext(merged)
    if prs:
        return 'closed-pr', REVIEW, _prtext(prs)
    return 'no-pr', REVIEW, ''


def _ts(s):
    return dt.datetime.fromisoformat(s.replace('Z', '+00:00'))


def _prtext(prs):
    return ' '.join(f"#{p['number']}{p['state'][0].lower()}" for p in sorted(prs, key=lambda p: p['number']))


def clone_for(repo, local):
    if local:
        return local
    cache = os.path.expanduser(f"~/.cache/factoidal-branch-audit/{repo.replace('/', '-')}.git")
    if not os.path.isdir(cache):
        os.makedirs(os.path.dirname(cache), exist_ok=True)
        run(['git', 'clone', '--bare', '--filter=blob:none', '-q', f'https://github.com/{repo}', cache])
        run(['git', 'config', 'remote.origin.fetch', '+refs/heads/*:refs/remotes/origin/*'], cwd=cache)
    run(['git', 'fetch', '-q', '--prune', 'origin'], cwd=cache)
    return cache


def default_branch(repo):
    return run(['gh', 'repo', 'view', repo, '--json', 'defaultBranchRef', '-q', '.defaultBranchRef.name']).strip()


def refs(git, pattern):
    out = run(['git', 'for-each-ref', '--format=%(refname)%09%(objectname)%09%(committerdate:iso-strict)%09%(upstream)%09%(worktreepath)', pattern], cwd=git)
    rows = []
    for line in out.splitlines():
        ref, sha, date, upstream, wt = (line.split('\t') + ['', ''])[:5]
        rows.append({'ref': ref, 'sha': sha, 'date': _ts(date).astimezone(dt.timezone.utc), 'upstream': upstream, 'worktree': wt})
    return rows


def ahead_behind(git, base, sha):
    out = run(['git', 'rev-list', '--left-right', '--count', f'{base}...{sha}'], cwd=git, check=False).split()
    return (int(out[1]), int(out[0])) if len(out) == 2 else (None, None)


def patch_equal(git, base, sha, limit=400):
    """The branch's whole diff (merge base to head) has the patch-id of one commit on base."""
    mb = run(['git', 'merge-base', base, sha], cwd=git, check=False).strip()
    if not mb:
        return None
    def pid(diff):
        out = subprocess.run(['git', 'patch-id', '--stable'], input=diff, capture_output=True, text=True, cwd=git).stdout.split()
        return out[0] if out else None
    want = pid(run(['git', 'diff', mb, sha], cwd=git, check=False))
    if not want:
        return None
    for c in run(['git', 'rev-list', f'--max-count={limit}', f'{mb}..{base}'], cwd=git).split():
        if pid(run(['git', 'show', '--format=', c], cwd=git, check=False)) == want:
            return True
    return False


def audit(repo, local, args, now):
    git = clone_for(repo, local)
    if args.fetch and local:
        run(['git', 'fetch', '-q', '--prune', 'origin'], cwd=git)
    main = default_branch(repo)
    base = f'refs/remotes/origin/{main}'
    prs = json.loads(run(['gh', 'pr', 'list', '-R', repo, '--state', 'all', '--limit', '2000',
                          '--json', 'number,state,headRefName,headRefOid,updatedAt,mergedAt']))
    by_head = {}
    for p in prs:
        by_head.setdefault(p['headRefName'], []).append(p)
    remote = {r['ref'][len('refs/remotes/origin/'):]: r for r in refs(git, 'refs/remotes/origin/')}
    remote.pop('HEAD', None)
    local_rows = {} if local is None else {r['ref'][len('refs/heads/'):]: r for r in refs(git, 'refs/heads/')}
    names = set()
    if not args.local_only:
        names |= set(remote)
    if not args.remote_only:
        names |= set(local_rows)
    rows = []
    for name in sorted(names):
        if name == main:
            continue
        r, l = remote.get(name), local_rows.get(name)
        head = r or l
        unpushed = None
        if r and l and l['sha'] != r['sha']:
            unpushed, _ = ahead_behind(git, r['sha'], l['sha'])
        sha = (l or r)['sha'] if l and unpushed else head['sha']
        ahead, behind = ahead_behind(git, base, sha)
        has = ahead == 0
        pe = patch_equal(git, base, sha) if args.patch_id and not has and r else None
        b = {'name': name, 'sha': sha, 'date': (l if l and unpushed else head)['date'], 'remote': r is not None,
             'local': l is not None, 'unpushed': unpushed}
        cls, action, prt = classify(b, by_head.get(name, []), has, now, args.stale_days, pe)
        rows.append({'repo': repo, 'branch': name, 'where': ('remote+local' if r and l else 'remote' if r else 'local'),
                     'last_commit': b['date'].strftime('%Y-%m-%d'), 'age_days': (now - b['date']).days,
                     'ahead': ahead, 'behind': behind, 'unpushed': unpushed, 'prs': prt, 'class': cls,
                     'action': action, 'worktree': (l or {}).get('worktree', ''), 'sha': sha[:9]})
    return rows


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--repo', action='append', help='OWNER/NAME[=LOCAL_CLONE]; repeatable')
    ap.add_argument('--json', action='store_true')
    ap.add_argument('--stale-days', type=int, default=7)
    ap.add_argument('--patch-id', action='store_true', help='also test squash merges by patch-id (slow; may fetch blobs)')
    ap.add_argument('--fetch', action='store_true', help='git fetch --prune origin in a given local clone first')
    g = ap.add_mutually_exclusive_group()
    g.add_argument('--local-only', action='store_true')
    g.add_argument('--remote-only', action='store_true')
    a = ap.parse_args(argv)
    here = run(['git', 'rev-parse', '--show-toplevel']).strip()
    specs = a.repo or [f'danbri/factoidal-core={here}']
    now = dt.datetime.now(dt.timezone.utc)
    rows = []
    for s in specs:
        repo, _, local = s.partition('=')
        try:
            rows += audit(repo, os.path.expanduser(local) if local else None, a, now)
        except RuntimeError as e:
            print(f'branch-audit: {repo}: {e}', file=sys.stderr)
    if a.json:
        json.dump(rows, sys.stdout, indent=1)
        print()
        return 0
    cols = ['repo', 'branch', 'where', 'last_commit', 'ahead', 'behind', 'unpushed', 'prs', 'class', 'action']
    rows.sort(key=lambda r: (r['repo'], r['action'] == NONE, r['class'], r['last_commit']))
    widths = {c: min(48, max([len(c)] + [len(str(r[c] if r[c] is not None else '')) for r in rows])) for c in cols}
    print('  '.join(c.ljust(widths[c]) for c in cols))
    for r in rows:
        print('  '.join(str(r[c] if r[c] is not None else '')[:48].ljust(widths[c]) for c in cols))
    summary = {}
    for r in rows:
        summary[(r['repo'], r['class'])] = summary.get((r['repo'], r['class']), 0) + 1
    print()
    for (repo, cls), n in sorted(summary.items()):
        print(f'{repo}  {cls}: {n}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
