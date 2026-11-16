#!/usr/bin/env python3
"""Tests of tools/branch-audit.py's classification (pure; no git, no network).

    python3 tools/branch-audit-test.py
"""
import datetime as dt, importlib.util, os, unittest

spec = importlib.util.spec_from_file_location('branch_audit', os.path.join(os.path.dirname(__file__), 'branch-audit.py'))
ba = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ba)
NOW = dt.datetime(2026, 11, 16, tzinfo=dt.timezone.utc)


def br(**kw):
    b = {'name': 'wip/x', 'sha': 'aaa', 'date': NOW, 'remote': True, 'local': False, 'unpushed': None}
    b.update(kw)
    return b


def pr(n, state, oid='aaa', updated='2026-11-15T00:00:00Z'):
    return {'number': n, 'state': state, 'headRefOid': oid, 'updatedAt': updated, 'mergedAt': None}


class Classify(unittest.TestCase):
    def c(self, b, prs=(), has=False, pe=None):
        return ba.classify(b, list(prs), has, NOW, 7, pe)[:2]

    def test_ancestor_is_merged(self):
        self.assertEqual(self.c(br(), has=True), ('merged', ba.DELETE))

    def test_squash_merged_by_pr_head(self):
        self.assertEqual(self.c(br(), [pr(5, 'MERGED')]), ('merged-pr', ba.DELETE))

    def test_moved_on_after_merge(self):
        self.assertEqual(self.c(br(sha='bbb'), [pr(5, 'MERGED')]), ('merged-pr-later', ba.REVIEW))

    def test_patch_id(self):
        self.assertEqual(self.c(br(), pe=True), ('merged-patch', ba.DELETE))

    def test_open_pr_fresh_and_stale(self):
        self.assertEqual(self.c(br(), [pr(6, 'OPEN')]), ('open-pr', ba.NONE))
        self.assertEqual(self.c(br(), [pr(6, 'OPEN', updated='2026-11-01T00:00:00Z')]), ('open-pr-stale', ba.PING))

    def test_open_pr_wins_over_older_merged_pr(self):
        self.assertEqual(self.c(br(sha='bbb'), [pr(5, 'MERGED'), pr(9, 'OPEN', oid='bbb')]), ('open-pr', ba.NONE))

    def test_closed_and_no_pr(self):
        self.assertEqual(self.c(br(), [pr(7, 'CLOSED')]), ('closed-pr', ba.REVIEW))
        self.assertEqual(self.c(br()), ('no-pr', ba.REVIEW))

    def test_local_branches(self):
        self.assertEqual(self.c(br(remote=False, local=True)), ('local-only', ba.PUSH))
        self.assertEqual(self.c(br(remote=False, local=True), has=True), ('merged', ba.DELETE))
        self.assertEqual(self.c(br(local=True, unpushed=2)), ('local-unpushed', ba.PUSH))
        # commits missing from the remote branch but already in the default branch are not lost
        self.assertEqual(self.c(br(local=True, unpushed=2), has=True), ('merged', ba.DELETE))


if __name__ == '__main__':
    unittest.main()
