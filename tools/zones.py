#!/usr/bin/env python3
"""Static code-zone inventory. Standard library only; never starts Lean or a build.

Counts every tracked or non-ignored untracked file in the configured roots.
Imports are lexical evidence, not a call graph or a proof of effect confinement.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict, deque
from fnmatch import fnmatchcase
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
JS_SUFFIXES = {'.js', '.mjs', '.cjs', '.ts', '.tsx', '.jsx', '.mts', '.cts'}
SOURCE_SUFFIXES = JS_SUFFIXES | {'.lean', '.py', '.sh', '.c', '.h', '.m', '.mm',
    '.html', '.css', '.svg', '.xml', '.xsl', '.rq', '.wat', '.ml', '.njk', '.command'}
LEAN_ROOTS = ('formal/lean4', 'labs/demos/foafnaut', 'tools/safety-scan/fixtures')
LEAN_CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:u\{[0-9a-fA-F]+\}|.))'")


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], stderr=subprocess.PIPE)


def inventory(root, roots):
    """Read Git's current index and non-ignored working files, never a saved list."""
    paths = sorted(set(git(root, 'ls-files', '-z', '--cached', '--others',
                           '--exclude-standard', '--', *roots).decode().split('\0')) - {''})
    if not paths:
        raise ValueError('Empty inventory: check the repository and configured roots')
    for directory in roots:
        if not any(p.startswith(directory.rstrip('/') + '/') for p in paths):
            raise ValueError(f'Empty inventory root: {directory}')
    return paths


def matches(path, patterns):
    return any(fnmatchcase(path, p) for p in patterns)


def validate_config(config):
    if config['schema_version'] != 1:
        raise ValueError('Unsupported zone schema')
    ids = [z['id'] for z in config['zones']]
    if len(set(ids)) != len(ids):
        raise ValueError('Duplicate zone id')
    rule_ids = [r['id'] for r in config['rules']]
    if len(set(rule_ids)) != len(rule_ids):
        raise ValueError('Duplicate rule id')
    for r in config['rules']:
        if r['zone'] not in ids or not r['paths']:
            raise ValueError(f'Invalid rule: {r["id"]}')
    for source, targets in config['allowed_dependencies'].items():
        if source not in ids or any(t not in ids for t in targets):
            raise ValueError('Unknown zone in dependency policy')
    for r in config['interfaces']:
        if r['target'] not in ids or any(s not in ids for s in r['sources']):
            raise ValueError(f'Unknown zone in interface: {r["id"]}')


def classify(path, config):
    return [r for r in config['rules'] if matches(path, r['paths'])
            and not matches(path, r.get('exclude', []))]


def mask_lean(text):
    """Blank comments (including nesting) and strings, preserving offsets and lines."""
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        start = i
        if text.startswith('--', i):
            i = text.find('\n', i)
            if i < 0:
                i = n
        elif text.startswith('/-', i):
            i += 2
            depth = 1
            while i < n and depth:
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif text[i] == "'" and (char := LEAN_CHAR.match(text, i)):
            i += len(char.group())
        elif text[i] == '"':
            i += 1
            while i < n:
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, n)):
            if text[j] not in '\r\n':
                out[j] = ' '
    return ''.join(out)


def lean_imports(text):
    # One command can name several modules. Headers in this tree are line-based.
    clean = mask_lean(text)
    for number, line in enumerate(clean.splitlines(), 1):
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+)$', line)
        if match:
            for module in match.group(1).split():
                if re.fullmatch(r'[\w\u00a0-\uffff]+(?:\.[\w\u00a0-\uffff]+)*', module):
                    yield module, number, 'lean'


def js_tokens(text):
    """Small lexical scanner: comments, strings, templates and regex bodies are opaque.

    Template substitutions and executable code embedded in strings are not scanned.
    A regex following an expression-start token is skipped; this is not a JS parser.
    """
    i, line, n = 0, 1, len(text)
    previous = ''
    while i < n:
        c = text[i]
        if c.isspace():
            line += c == '\n'
            i += 1
            continue
        if text.startswith('//', i) or (i == 0 and text.startswith('#!', i)):
            end = text.find('\n', i)
            i = n if end < 0 else end
            continue
        if text.startswith('/*', i):
            end = text.find('*/', i + 2)
            end = n if end < 0 else end + 2
            line += text[i:end].count('\n')
            i = end
            continue
        start, start_line = i, line
        if c in "'\"`":
            i += 1
            value = []
            while i < n and text[i] != c:
                if text[i] == '\\' and i + 1 < n:
                    # Literal path escapes common in import specifiers.
                    i += 1
                    if text[i] in "\\'\"`":
                        value.append(text[i])
                    elif text[i] == '\n':
                        pass
                    else:
                        value.extend(('\\', text[i]))
                else:
                    value.append(text[i])
                i += 1
            i = min(i + 1, n)
            line += text[start:i].count('\n')
            previous = 'literal'
            yield ('template' if c == '`' else 'string', ''.join(value), start_line)
            continue
        if c == '/' and previous in ('', '=', '(', '[', '{', ',', ':', ';', '!', '?', 'return', '=>'):
            i += 1
            in_class = False
            while i < n:
                if text[i] == '\\':
                    i += 2
                    continue
                if text[i] == '[':
                    in_class = True
                if text[i] == ']':
                    in_class = False
                if text[i] == '/' and not in_class:
                    i += 1
                    while i < n and text[i].isalpha():
                        i += 1
                    break
                if text[i] == '\n':
                    break
                i += 1
            previous = 'literal'
            yield 'regex', '', start_line
            continue
        if c.isalpha() or c in '_$':
            i += 1
            while i < n and (text[i].isalnum() or text[i] in '_$'):
                i += 1
            previous = text[start:i]
            yield 'id', previous, start_line
        else:
            i += 1
            previous = c
            yield 'punct', c, start_line


def js_imports(text):
    tokens = list(js_tokens(text))
    for i, (kind, word, line) in enumerate(tokens):
        if kind != 'id' or word not in ('import', 'export', 'require'):
            continue
        if i and tokens[i - 1][1] in ('.', '?.'):
            continue
        rest = tokens[i + 1:]
        if not rest:
            continue
        if word in ('import', 'require') and rest[0][1] == '(':
            if len(rest) > 2 and rest[1][0] == 'string' and rest[2][1] in (')', ','):
                yield rest[1][1], line, 'dynamic-import' if word == 'import' else 'require'
            else:
                yield None, line, 'computed-' + word
        elif word == 'import' and rest[0][0] == 'string':
            yield rest[0][1], line, 'import'
        elif word in ('import', 'export') and rest[0][1] not in ('(', '.', 'const', 'let', 'var', 'function', 'class', 'default', 'async'):
            # Search the import/export clause only, stopping at a statement boundary.
            for j, token in enumerate(rest):
                if token[1] in (';', '=') or (j and token[1] in ('import', 'export')):
                    break
                if token[0:2] == ('id', 'from') and j + 1 < len(rest) and rest[j + 1][0] == 'string':
                    yield rest[j + 1][1], line, word
                    break


def module_name(path):
    if not path.endswith('.lean'):
        return None
    for root in LEAN_ROOTS:
        if path.startswith(root + '/'):
            return path[len(root) + 1:-5].replace('/', '.')
    return None


def resolve_js(source, specifier, paths):
    if not specifier.startswith('.'):
        return None, 'external'
    base = posixpath.normpath(posixpath.join(posixpath.dirname(source), specifier.split('?')[0].split('#')[0]))
    # Deno commonly specifies extensions; TypeScript may spell an emitted .js file.
    candidates = [base]
    if base.endswith(('.js', '.mjs', '.cjs')):
        candidates += [base.rsplit('.', 1)[0] + ext for ext in ('.ts', '.mts', '.cts', '.tsx')]
    candidates += [base + ext for ext in ('.ts', '.tsx', '.js', '.mjs', '.cjs', '.json')]
    candidates += [base + '/index' + ext for ext in ('.ts', '.tsx', '.js', '.mjs', '.cjs')]
    for candidate in candidates:
        if candidate in paths:
            return candidate, 'resolved'
    return None, 'unresolved-local'


def policy(source, target, source_path, target_path, config):
    if source == target:
        return 'within-zone', ''
    boundaries = [r for r in config['interfaces'] if source in r['sources'] and target == r['target']]
    if boundaries:
        for rule in boundaries:
            if (matches(source_path, rule.get('source_paths', ['*'])) and
                    matches(target_path, rule.get('target_paths', ['*']))):
                return 'interface', rule['id']
        return 'interface-review', '; '.join(r['id'] for r in boundaries)
    if target in config['allowed_dependencies'].get(source, []):
        return 'expected', ''
    return 'unexpected', 'No allowed dependency for this zone pair'


def strongly_connected(nodes, edges):
    """Tarjan SCCs: all mutually reachable zone groups, not all simple cycles."""
    graph = {n: set() for n in nodes}
    for a, b in edges:
        graph[a].add(b)
    index, low, stack, active, groups = {}, {}, [], set(), []

    def visit(v):
        index[v] = low[v] = len(index)
        stack.append(v)
        active.add(v)
        for w in sorted(graph[v]):
            if w not in index:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in active:
                low[v] = min(low[v], index[w])
        if low[v] == index[v]:
            group = []
            while True:
                w = stack.pop()
                active.remove(w)
                group.append(w)
                if w == v:
                    break
            if len(group) > 1:
                groups.append(sorted(group))
    for v in sorted(nodes):
        if v not in index:
            visit(v)
    return sorted(groups)


def boundary_probes(files, imports, probes):
    """Shortest witness through resolved file imports, with no zone-level shortcuts."""
    by_path = {f['path']: f for f in files}
    graph = defaultdict(set)
    for edge in imports:
        graph[edge['source']].add(edge['target'])
    result = []
    for probe in probes:
        starts = sorted(f['path'] for f in files if
            f['zone'] in probe.get('source_zones', [f['zone']]) and
            matches(f['path'], probe.get('source_paths', ['*'])))
        queue = deque((s, [s]) for s in starts)
        seen, witness = set(), []
        while queue:
            path, chain = queue.popleft()
            if path in seen:
                continue
            seen.add(path)
            if len(chain) > 1 and by_path[path]['zone'] in probe['target_zones']:
                witness = chain
                break
            queue.extend((target, chain + [target]) for target in sorted(graph[path]) if target not in seen)
        result.append(dict(probe, source_files=len(starts), witness=witness,
                           status='empty-selection' if not starts else 'crossing-found' if witness else 'no-resolved-path'))
    return result


def analyse(root, config):
    validate_config(config)
    paths = inventory(root, config['roots'])
    all_paths = set(git(root, 'ls-files', '-z', '--cached', '--others', '--exclude-standard').decode().split('\0')) - {''}
    module_paths = defaultdict(list)
    for path in sorted(all_paths):
        name = module_name(path)
        if name:
            module_paths[name].append(path)
    files, unmapped, ambiguous, missing, raw_imports = [], [], [], [], []
    used_rules = Counter()
    digest = hashlib.sha256()
    for path in paths:
        rules = classify(path, config)
        if not rules:
            unmapped.append(path)
        if len(rules) > 1:
            ambiguous.append({'path': path, 'rules': [r['id'] for r in rules]})
        disk_path = root / path
        symlink = disk_path.is_symlink()
        if not symlink and not disk_path.is_file():
            missing.append(path)
            continue
        # Never traverse fixture symlinks into another checkout or external assets.
        data = os.readlink(disk_path).encode() if symlink else disk_path.read_bytes()
        digest.update(path.encode() + b'\0' + data + b'\0')
        try:
            text = data.decode('utf-8') if b'\0' not in data else None
        except UnicodeDecodeError:
            text = None
        suffix = PurePosixPath(path).suffix
        source = not symlink and (suffix in SOURCE_SUFFIXES or (text is not None and text.startswith('#!')))
        zone = rules[0]['zone'] if len(rules) == 1 else None
        if len(rules) == 1:
            used_rules[rules[0]['id']] += 1
        files.append(dict(path=path, module=module_name(path), zone=zone,
            rule=rules[0]['id'] if len(rules) == 1 else None,
            tags=[t['tag'] for t in config.get('secondary_tags', []) if matches(path, t['paths'])],
            source=source, binary=text is None, symlink=symlink, bytes=len(data), lines=len(text.splitlines()) if text is not None and not symlink else 0))
        if text is not None and not symlink:
            reader = lean_imports if suffix == '.lean' else js_imports if suffix in JS_SUFFIXES else None
            if reader:
                for name, line, kind in reader(text):
                    raw_imports.append(dict(source=path, specifier=name, line=line, kind=kind))
    by_path = {f['path']: f for f in files}
    imports, other = [], []
    for item in raw_imports:
        name = item['specifier']
        if name is None:
            other.append(dict(item, status='computed'))
            continue
        if item['kind'] == 'lean':
            candidates = module_paths.get(name, [])
            target = candidates[0] if len(candidates) == 1 else None
            status = ('ambiguous-module' if candidates else 'external' if name.split('.')[0] in
                      ('Init', 'Lean', 'Std', 'Lake', 'Mathlib', 'Batteries') else 'unresolved-local')
        else:
            target, status = resolve_js(item['source'], name, all_paths)
        if target not in by_path or by_path[target]['zone'] is None or by_path[item['source']]['zone'] is None:
            other.append(dict(item, target=target, status='outside-inventory' if target else status))
            continue
        a, b = by_path[item['source']]['zone'], by_path[target]['zone']
        state, reason = policy(a, b, item['source'], target, config)
        imports.append(dict(item, target=target, source_zone=a, target_zone=b, policy=state, reason=reason))
    pairs = defaultdict(list)
    for item in imports:
        if item['source_zone'] != item['target_zone']:
            pairs[item['source_zone'], item['target_zone']].append(item)
    edges = []
    for (a, b), items in pairs.items():
        edges.append(dict(source=a, target=b, count=len(items), source_files=len({x['source'] for x in items}),
            target_files=len({x['target'] for x in items}), kinds=dict(sorted(Counter(x['kind'] for x in items).items())),
            policies=dict(sorted(Counter(x['policy'] for x in items).items())), examples=items[:3]))
    edges.sort(key=lambda e: (-e['count'], e['source'], e['target']))
    sizes = []
    for zone in config['zones']:
        fs = [f for f in files if f['zone'] == zone['id']]
        sizes.append(dict(zone, files=len(fs), lines=sum(f['lines'] for f in fs),
            source_files=sum(f['source'] for f in fs), source_lines=sum(f['lines'] for f in fs if f['source']),
            lean_modules=sum(f['path'].endswith('.lean') for f in fs), binary_files=sum(f['binary'] for f in fs)))
    declared_unmapped = config.get('unmapped_files', [])
    leaks = [i for i in imports if i['policy'] in ('unexpected', 'interface-review')]
    leaks.sort(key=lambda i: (i['policy'] != 'unexpected', i['source_zone'], i['target_zone'], i['source'], i['line']))
    return dict(schema_version=1, source_commit=git(root, 'rev-parse', 'HEAD').decode().strip(),
        inventory_sha256=digest.hexdigest(), mapping_sha256=hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest(),
        roots=config['roots'], sizes=sizes, totals=dict(files=len(paths), lines=sum(f['lines'] for f in files),
        source_files=sum(f['source'] for f in files), source_lines=sum(f['lines'] for f in files if f['source']),
        lean_modules=sum(f['path'].endswith('.lean') for f in files), import_sites=len(raw_imports),
        resolved_import_sites=len(imports), cross_zone_import_sites=sum(e['count'] for e in edges),
        zone_edges=len(edges), leaks=len(leaks)), files=files, edges=edges, imports=imports,
        cycles=strongly_connected([z['id'] for z in sizes], pairs),
        reciprocal_pairs=[list((a, b)) for a, b in sorted(pairs) if a < b and (b, a) in pairs],
        leaks=leaks, other_imports=other, unmapped_files=unmapped, ambiguous_files=ambiguous,
        taxonomy_notes=config.get('taxonomy_notes', []), review_notes=config.get('review_notes', []),
        candidate_theorems=config.get('candidate_theorems', []),
        boundary_probes=boundary_probes(files, imports, config.get('boundary_probes', [])),
        missing_files=missing, symlink_files=[f['path'] for f in files if f['symlink']],
        stale_unmapped_files=sorted(set(declared_unmapped) - set(unmapped)),
        undeclared_unmapped_files=sorted(set(unmapped) - set(declared_unmapped)),
        unused_rules=[r['id'] for r in config['rules'] if not used_rules[r['id']]])


def file_link(path, prefix, line=None):
    # URL fragment works in GitHub and the generated Markdown snapshot.
    return f'[`{path}`]({prefix}{path}' + (f'#L{line}' if line else '') + ')'


def render_markdown(report, link_prefix='../'):
    t = report['totals']
    lines = ['# Code-zone dependency report', '',
        f'Source HEAD: `{report["source_commit"]}`; inventory SHA-256: `{report["inventory_sha256"]}`.', '',
        'HEAD identifies the base commit; the inventory hash includes working edits. Regenerate with '
        '`python3 tools/zones.py --check --markdown docs/zones.md --json /tmp/zones.json`.', '',
        f'{t["files"]:,} files; {t["source_files"]:,} source files; {t["lean_modules"]:,} Lean modules; '
        f'{t["source_lines"]:,} source lines ({t["lines"]:,} text lines including support files).', '',
        'Inventory: tracked plus non-ignored untracked files in ' + ', '.join(f'`{r}/`' for r in report['roots']) + '.', '',
        'Physical lines include comments and blanks. Binary files and symlinks have zero lines; symlinks are never followed. Tests, fixtures and tooling remain in the totals. '
        'The source-extension set is in `tools/zones.py`; all other files still receive a zone.', '',
        'Edges point from importer to imported file and count import sites, including tests and type-only imports. '
        'Nested Lean comments and string literals are removed. JS/TS covers static imports, re-exports, literal dynamic imports and literal require calls. '
        'Package imports, computed paths, generated files, template substitutions, embedded scripts, FFI and operation-number protocols need separate review. '
        'This scan does not execute a compiler, resolve package exports or establish effect confinement.', '',
        '## Zones and sizes', '', '| Zone | Definition | All files | Source files | Source lines | All text lines | Lean | Binary |',
        '|---|---|---:|---:|---:|---:|---:|---:|']
    for z in report['sizes']:
        lines.append(f'| `{z["id"]}` — {z["name"]} | {z["definition"]} | {z["files"]:,} | {z["source_files"]:,} | {z["source_lines"]:,} | {z["lines"]:,} | {z["lean_modules"]} | {z["binary_files"]} |')
    lines += [''] + ['- ' + note for note in report['taxonomy_notes']]
    lines += ['', '## Reviewed crossings and candidate theorems', '',
        'Prior measurement: [issue 452, part 2](https://github.com/danbri/factoidal-core/issues/452). '
        'That survey counted top-level Lean subtrees; this report uses semantic zones and includes hosts, tests and tooling. '
        'The two sets of counts have different denominators.', '']
    for note in report['review_notes']:
        lines.append('- ' + note['statement'] + ' ' + ', '.join(file_link(p, link_prefix) for p in note['modules']) + '.')
    lines += ['', 'Candidates below are statements to develop through the '
        '[theorem pipeline](../skills/theorem-pipeline/SKILL.md) and '
        '[issue 513](https://github.com/danbri/factoidal-core/issues/513). '
        'No new Lean theorem or axiom check is claimed by this report.', '',
        '| Candidate statement | Modules | Obligation |', '|---|---|---|']
    for item in report['candidate_theorems']:
        lines.append('| ' + item['statement'] + ' | ' + ', '.join(file_link(p, link_prefix) for p in item['modules']) + ' | ' + item['obligation'] + ' |')
    lines += ['', '### Structural probes', '',
        'These traverse resolved file imports, not the aggregated zone graph. Missing/generated imports and runtime effects remain outside the evidence.', '']
    for probe in report['boundary_probes']:
        lines.append(f'- {probe["name"]}: **{probe["status"]}**, {probe["source_files"]} selected files.' +
                     (' Witness: ' + ' → '.join(file_link(p, link_prefix) for p in probe['witness']) + '.' if probe['witness'] else ''))
    ids = [z['id'] for z in report['sizes']]
    matrix = {(e['source'], e['target']): e['count'] for e in report['edges']}
    lines += ['', '## Dependency matrix', '', 'Rows import columns. `·` is zero; within-zone imports are omitted.', '',
        '| From / to | ' + ' | '.join(ids) + ' |', '|---|' + '---:|' * len(ids)]
    for a in ids:
        lines.append('| ' + a + ' | ' + ' | '.join(str(matrix.get((a,b), '·')) for b in ids) + ' |')
    lines += ['', '## Cross-zone edges', '', f'{t["cross_zone_import_sites"]:,} import sites across {t["zone_edges"]} directed zone pairs.', '',
        '| From → to | Sites | Importing files | Example crossings |', '|---|---:|---:|---|']
    for edge in report['edges']:
        examples = '<br>'.join(file_link(e['source'], link_prefix, e['line']) + ' → ' + file_link(e['target'], link_prefix) for e in edge['examples'][:2])
        lines.append(f'| {edge["source"]} → {edge["target"]} | {edge["count"]} | {edge["source_files"]} | {examples} |')
    lines += ['', '## Cycles', '',
        'These are strongly connected components of the zone graph. Grouping modules into zones can introduce cycles even when the module graph is acyclic.']
    lines += [''] + ['- ' + ', '.join(f'`{n}`' for n in group) for group in report['cycles']]
    if not report['cycles']:
        lines.append('None.')
    lines += ['', 'Reciprocal zone pairs: ' + (', '.join(' ↔ '.join(p) for p in report['reciprocal_pairs']) or 'none') + '.', '',
        '## Leaks and interface review', '',
        f'{len(report["leaks"])} import sites are flagged by the proposed policy in `zones/zones.json`. '
        'An unexpected pair has no allowed dependency; an interface review crosses an expected pair outside its named modules. '
        'These are review candidates, not established defects. Counts include tests. Broad allowed pairs are documented expectations, not a ratchet or security proof.', '',
        '| From → to | Flag | Sites |', '|---|---|---:|']
    counts = Counter((e['source_zone'],e['target_zone'],e['policy']) for e in report['leaks'])
    for (a,b,status), count in sorted(counts.items(), key=lambda kv: (-kv[1],kv[0])):
        lines.append(f'| {a} → {b} | {status} | {count} |')
    lines += ['', '<details><summary>Every flagged module crossing</summary>', '', '| Source | Target | Flag / interface |', '|---|---|---|']
    for e in report['leaks']:
        lines.append(f'| {file_link(e["source"], link_prefix, e["line"])} | {file_link(e["target"], link_prefix)} | {e["policy"]}: {e["reason"]} |')
    lines += ['', '</details>', '', '## Inventory and import diagnostics', '']
    for field in ('unmapped_files','ambiguous_files','missing_files','symlink_files','stale_unmapped_files','undeclared_unmapped_files','unused_rules'):
        lines.append(f'- `{field}`: ' + (json.dumps(report[field], ensure_ascii=False) if report[field] else 'none') + '.')
    counts = Counter(e['status'] for e in report['other_imports'])
    lines += ['', 'Import sites outside the resolved zone graph: ' + ', '.join(f'{k}: {v}' for k,v in sorted(counts.items())) + '.', '',
        '<details><summary>Unresolved, computed and outside-inventory imports</summary>', '', '| Source | Specifier | Status |', '|---|---|---|']
    for e in report['other_imports']:
        if e['status'] != 'external':
            lines.append(f'| {file_link(e["source"], link_prefix, e["line"])} | `{e["specifier"] or "(computed)"}` | {e["status"]} |')
    lines += ['', '</details>', '', 'JSON output retains every file assignment, resolved import, external import and diagnostic.', '']
    return '\n'.join(lines)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--mapping', type=Path, help='Defaults to ROOT/zones/zones.json')
    parser.add_argument('--json', type=Path, dest='json_path', help='Write complete machine-readable report')
    parser.add_argument('--markdown', type=Path, help='Write Markdown report (stdout by default)')
    parser.add_argument('--link-prefix', default='../', help='Link prefix relative to Markdown output')
    parser.add_argument('--check', action='store_true', help='Fail unless every inventory file maps exactly once')
    parser.add_argument('--strict', action='store_true', help='Also fail on proposed-policy leaks')
    args = parser.parse_args(argv)
    try:
        config = json.loads((args.mapping or args.root / 'zones/zones.json').read_text())
        report = analyse(args.root, config)
        if args.json_path:
            args.json_path.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
        md = render_markdown(report, args.link_prefix)
        if args.markdown:
            args.markdown.write_text(md)
        elif not args.json_path:
            print(md, end='')
        errors = any(report[k] for k in ('unmapped_files','ambiguous_files','missing_files','stale_unmapped_files'))
        if (args.check or args.strict) and errors:
            print('zones: inventory errors; see report diagnostics', file=sys.stderr)
            return 1
        if args.strict and report['leaks']:
            print(f'zones: {len(report["leaks"])} policy review sites', file=sys.stderr)
            return 1
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f'zones: {error}', file=sys.stderr)
        return 2
    return 0


if __name__ == '__main__':
    sys.exit(main())
