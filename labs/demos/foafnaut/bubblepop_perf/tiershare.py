#!/usr/bin/env python3
"""Share of BubblePopJS run time by machine: the register machine (`vmLoop`) or the tree
evaluator (`evalExpr`, `evalStmt`, ...), from a macOS `sample` call tree.

  tiershare.py SAMPLE_FILE

Each sample's own time (a node's count less its children's) goes to the innermost machine
frame above it: time in a helper (a property read, a built-in, the allocator) counts for the
machine that called it. Time with no machine frame above it (parse, resolve, start) is
"other". Only the thread that runs the engine is read.

To take a sample of a whole run:  leanjs run FILE & sample $! 60 1 -file OUT
"""
import re
import sys

VM = re.compile(r'_JS_(vmLoop|vmEnter|vmRegion)_')
TREE = re.compile(r'_JS_(evalExpr|evalStmt|evalStmts|evalBlock|evalBody|whileLoop|doLoop|forLoop|'
                  r'forInLoop|forOfLoop|runCases|switchFind|evalDecls|evalArgs|evalProps|callBody|genRun)_')
LINE = re.compile(r'^([ +|:!]*)(\d+) (.*)$')


def main(path):
    lines = open(path, errors='replace').read().split('\n')
    # threads start with a line like "    1234 Thread_..."
    threads, cur = [], None
    for l in lines:
        if l.startswith('Total number in stack'):
            break
        m = LINE.match(l)
        if not m:
            continue
        if 'Thread_' in m.group(3) and len(m.group(1)) <= 4:
            cur = [int(m.group(2)), []]
            threads.append(cur)
            continue
        if cur is not None:
            cur[1].append((len(m.group(1)), int(m.group(2)), m.group(3)))
    if not threads:
        raise SystemExit('no threads in %s' % path)
    js = [t for t in threads if any('_JS_' in n for (_, _, n) in t[1])]
    nodes = max(js or threads, key=lambda t: t[0])[1]
    share = {'vm': 0, 'tree': 0, 'other': 0}
    stack = []  # (depth, count, tier)
    selfs = []
    for i, (d, c, name) in enumerate(nodes):
        while stack and stack[-1][0] >= d:
            stack.pop()
        tier = 'vm' if VM.search(name) else 'tree' if TREE.search(name) else None
        if tier is None:
            tier = next((t for (_, _, t) in reversed(stack) if t in ('vm', 'tree')), 'other')
            mine = None
        else:
            mine = tier
        stack.append((d, c, mine or tier))
        child = 0
        if i + 1 < len(nodes) and nodes[i + 1][0] > d:
            cd = nodes[i + 1][0]
            for (d2, c2, _) in nodes[i + 1:]:
                if d2 <= d:
                    break
                if d2 == cd:
                    child += c2
        share[tier] += c - child
    tot = sum(share.values()) or 1
    print('samples %d: register machine %.1f%%, tree evaluator %.1f%%, other %.1f%%' % (
        tot, 100 * share['vm'] / tot, 100 * share['tree'] / tot, 100 * share['other'] / tot))


if __name__ == '__main__':
    main(sys.argv[1])
