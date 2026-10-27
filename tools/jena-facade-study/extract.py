#!/usr/bin/env python3
# Extract the one-line ARQ expression tests of Apache Jena
# (jena-arq/src/test/java/org/apache/jena/sparql/expr/*.java) into a JSON
# list of SPARQL ports. A one-line test is a line of the form
#   @Test public void NAME() { BODY }
# Each record has the Java source text, and either a "port" (a SPARQL
# expression and a check kind) or an "unported" reason (the test has no
# SPARQL-observable meaning, e.g. a Java expression-transform API test).
#
# Usage: python3 -I extract.py <jena root> <out.json>
#
# The cases are derived from Apache Jena (Apache License 2.0). Apache Jena:
# Copyright The Apache Software Foundation. Change: the Java test calls are
# rewritten as SPARQL expressions plus a check kind (see
# npm/factoidal/test/jena-arq-expr.test.mjs).
import collections, decimal, json, math, os, re, sys

ROOT = sys.argv[1]
OUT = sys.argv[2]
EXPR_DIR = os.path.join(ROOT, 'jena-arq/src/test/java/org/apache/jena/sparql/expr')
XSD = 'http://www.w3.org/2001/XMLSchema#'
ONE = re.compile(r'^\s*@Test\s+public void (\w+)\(\)\s*\{(.*)\}\s*$')

BUILTIN = {
    'XSDDatatype.XSD': 'http://www.w3.org/2001/XMLSchema',
    'RDF.getURI()': 'http://www.w3.org/1999/02/22-rdf-syntax-ns#',
    'RDF.nil.getURI()': 'http://www.w3.org/1999/02/22-rdf-syntax-ns#nil',
    'ARQConstants.ARQFunctionLibrary': 'http://jena.apache.org/ARQ/function#',
    'XSD.xstring.getURI()': XSD + 'string',
    'kwTRUE': 'true', 'kwFALSE': 'false', 'kwEmptyString': "''",
}


def java_string(lit):
    """Unescape a Java string literal (with its quotes)."""
    s, out, i = lit[1:-1], [], 0
    simple = {'n': '\n', 't': '\t', 'r': '\r', 'b': '\b', 'f': '\f', '"': '"', "'": "'", '\\': '\\'}
    while i < len(s):
        c = s[i]
        if c != '\\':
            out.append(c); i += 1; continue
        n = s[i + 1]
        if n in simple: out.append(simple[n]); i += 2
        elif n == 'u':
            j = i + 1
            while s[j] == 'u': j += 1
            out.append(chr(int(s[j:j + 4], 16))); i = j + 4
        else: raise ValueError('Java escape \\' + n)
    # join UTF-16 surrogate pairs written as two \u escapes
    return ''.join(out).encode('utf-16', 'surrogatepass').decode('utf-16')


def scan_string(s, i, q):
    j = i + 1
    while s[j] != q:
        j += 2 if s[j] == '\\' else 1
    return j


def split_top(s, sep):
    out, depth, cur, i = [], 0, '', 0
    while i < len(s):
        c = s[i]
        if c in '"\'':
            j = scan_string(s, i, c)
            cur += s[i:j + 1]; i = j + 1; continue
        if c in '([{': depth += 1
        if c in ')]}': depth -= 1
        if c == sep and depth == 0:
            out.append(cur.strip()); cur = ''
        else:
            cur += c
        i += 1
    if cur.strip() or out: out.append(cur.strip())
    return out


class Consts:
    def __init__(self, src):
        self.defs = {}
        for m in re.finditer(r'static\s+(?:final\s+)?String\s+(\w+)\s*=\s*(.*?);[;\s]*$', src, re.M):
            self.defs[m.group(1)] = m.group(2)
        self.nv = {}
        for m in re.finditer(r'NodeValue\s+(nv_\w+)\s*=\s*NodeValue\.makeNode\("([^"]*)",\s*XSDDatatype\.XSD(\w+)\)', src):
            self.nv[m.group(1)] = (m.group(2), m.group(3))

    def string(self, e):
        out = ''
        for p in split_top(e, '+'):
            m1 = re.fullmatch(r'XSDDatatype\.XSD(\w+)\.getURI\(\)', p)
            m2 = re.fullmatch(r'String\.format\("(.*)",\s*([0-9.]+)\)', p)
            m3 = re.fullmatch(r"StringUtils\.repeat\('(.)',\s*(\d+)\)", p)
            if p.startswith('"'): out += java_string(p)
            elif p in BUILTIN: out += BUILTIN[p]
            elif m1: out += XSD + m1.group(1)
            elif p in self.defs: out += self.string(self.defs[p])
            elif m2: out += m2.group(1) % float(m2.group(2))
            elif m3: out += m3.group(1) * int(m3.group(2))
            else: raise ValueError('unresolved string part: ' + p)
        return out


def java_num(e):
    """Evaluate a Java numeric or boolean test argument."""
    e = e.strip()
    if e.startswith('new BigDecimal('):
        return ('decimal', str(decimal.Decimal(java_string(e[len('new BigDecimal('):-1]))))
    if e.startswith('new BigInteger('):
        return ('integer', str(int(java_string(e[len('new BigInteger('):-1]))))
    py = re.sub(r'(\d)L\b', r'\1', e)
    py = py.replace('&&', ' and ').replace('||', ' or ')
    py = re.sub(r'!(?!=)', ' not ', py)
    for a, b in (('Math.PI', 'math.pi'), ('Math.exp', 'math.exp'), ('Math.log', 'math.log'),
                 ('Math.sqrt', 'math.sqrt'), ('Double.NaN', 'float("nan")')):
        py = py.replace(a, b)
    py = re.sub(r'\btrue\b', 'True', py); py = re.sub(r'\bfalse\b', 'False', py)
    v = eval(py, {'math': math, '__builtins__': {'float': float}})
    if isinstance(v, bool): return ('boolean', 'true' if v else 'false')
    if isinstance(v, int): return ('integer', str(v))
    return ('double', 'NaN' if v != v else repr(v))


def lit(lex, dt):
    return '"' + lex.replace('\\', '\\\\').replace('"', '\\"') + '"^^<' + XSD + dt + '>'


def nodevalue(e, cs):
    """Java NodeValue expression -> SPARQL term text."""
    e = e.strip()
    if e == 'NodeValue.TRUE': return 'true'
    if e == 'NodeValue.FALSE': return 'false'
    m = re.fullmatch(r'NodeValue\.makeString\((.*)\)', e)
    if m: return json.dumps(cs.string(m.group(1)), ensure_ascii=False)
    m = re.fullmatch(r'NodeValue\.makeInteger\((-?\d+)\)', e)
    if m: return m.group(1)
    m = re.fullmatch(r'NodeValue\.makeNode\("([^"]*)",\s*XSDDatatype\.XSD(\w+)\)', e)
    if m: return lit(m.group(1), m.group(2))
    m = re.fullmatch(r'NodeValue\.makeDate\("([^"]*)"\)', e)
    if m: return lit(m.group(1), 'date')
    if e in cs.nv: return lit(*cs.nv[e])
    raise ValueError('unresolved NodeValue: ' + e)


# The binding "env" of TestExpressions: ?a = "A", ?b = a blank node, ?x = <urn:ex:abcd>.
ENV = {'a': '"A"', 'b': 'BNODE()', 'x': '<urn:ex:abcd>'}
# Parser context of each test class (prefixes and base, from the Java source).
# 'global' is ARQConstants.getGlobalPrefixMap(); 'lib' adds lfn: (LibTestExpr).
LIB = {'TestExpressionsMath', 'TestExpressions4', 'TestLeviathanFunctions'}

UNPORTED = {
    'testVar': 'Jena parser API (Expr.isVariable, ExprVar.getVarName); no SPARQL result',
    'testSafeEquality': 'Jena optimizer API (ExprLib.isAssignmentSafeEquality); no SPARQL result',
    'testSSE': 'Jena SSE algebra syntax, not SPARQL',
    'evalExpr': 'Jena SSE algebra syntax, not SPARQL',
    'test_exprSprintf_tz_exact': 'afn:sprintf result depends on the JVM default time zone',
    'test_exprSprintf_tz_possibilites': 'afn:sprintf result depends on the JVM default time zone',
}
TRANSFORM_CLASSES = {'TestExprFunctionOp_ExprTransform', 'TestExprFunctionOp_NodeTransform', 'TestExprTransform'}


def sse_binding(s):
    s = s.strip()
    if re.fullmatch(r'\(\s*\)', s): return {}
    m = re.fullmatch(r'\(\?(\w+)\s+(.+)\)', s)
    if not m: raise ValueError('binding ' + s)
    return {m.group(1): m.group(2)}


def port(cls, helper, args, cs, wrapped):
    S = lambda i: cs.string(args[i])
    ctx = 'TestExpressions' if cls == 'TestExpressions' else ('lib' if cls in LIB else 'global')
    p = {'ctx': ctx}

    def err(expr, **extra):
        # ExprException is the superclass of Jena's evaluation errors too:
        # ExprUtils.parse compiles a constant regex, so an invalid pattern
        # fails at parse time in Jena and at evaluation time in SPARQL.
        k = {'QueryParseException': 'parseError', 'ExprException': 'error',
             'ExprEvalException': 'evalError', 'ExprEvalTypeException': 'evalError',
             'ExprNotComparableException': 'evalError', 'ARQException': 'error'}[wrapped]
        return dict(p, kind=k, expr=expr, **extra)

    if cls == 'TestExpressions':
        e = S(0)
        if helper == 'testSyntax': return err(e) if wrapped else dict(p, kind='parses', expr=e)
        if helper == 'testEval': return err(e) if wrapped else dict(p, kind='bound', expr=e)
        if helper == 'testNumeric':
            if wrapped: return err(e)
            t, v = java_num(args[1])
            return dict(p, kind=t, expr=e, expected=v)
        if helper == 'testBoolean':
            extra = {'env': ENV} if len(args) == 3 else {}
            if wrapped: return err(e, **extra)
            return dict(p, kind='boolean', expr=e, expected=java_num(args[1])[1], **extra)
        if helper == 'testURI':
            if wrapped: return err(e, env=ENV)
            q = dict(p, kind='iri', expr=e, expected=S(1), env=ENV)
            if e.endswith('.'):
                # testURI parses with parseAny: Jena stops at the end of the
                # prefixed name, and the final '.' is not part of it (SPARQL
                # 1.1 §19.8 PN_LOCAL cannot end with '.'). The port binds the
                # name without the '.' and also parses the original text as
                # the object of a triple pattern, where '.' ends the pattern.
                q.update(expr=e[:-1], parseTail=e)
            return q
        if helper == 'testString':
            if wrapped: return err(e, env=ENV)
            if len(args) == 1: return dict(p, kind='anyString', expr=e, env=ENV)
            return dict(p, kind='string', expr=e, expected=S(1), env=ENV)
    if cls in ('TestExpressions2', 'TestExpressions3') and helper == 'eval':
        e = S(0)
        extra = {'bind': sse_binding(S(1))} if len(args) == 3 else {}
        if wrapped: return err(e, **extra)
        exp = args[2] if len(args) == 3 else (args[1] if len(args) == 2 else 'true')
        return dict(p, kind='ebv', expr=e, expected=exp, **extra)
    if cls == 'TestSPARQLKeywordFunctions':
        if helper == 'test': return dict(p, kind='sameTerm', expr=S(0), expected=S(1))
        if helper == 'testEvalException': return dict(p, kind='evalError', expr=S(0))
        if helper == 'ExprUtils.parse': return err(S(0))
    if cls == 'TestCastXSD':
        if helper == 'testCast': return dict(p, kind='sameTerm', expr=S(0), expected=S(1))
        if helper == 'testNoCast': return dict(p, kind='evalError', expr=S(0))
    if cls in LIB or cls == 'TestFunctionsByURI':
        if helper == 'test':
            if wrapped: return err(S(0))
            return dict(p, kind='sameValueSameDatatype', expr=S(0), expected=S(1))
        if helper == 'testDoubleIsNaN': return dict(p, kind='nan', expr=S(0))
        if helper == 'testDouble':
            if wrapped: return err(S(0))
            delta = java_num(args[2])[1]
            if args[1].startswith('"'):
                return dict(p, kind='doubleNear', expr=S(0), expectedTerm=S(1), delta=delta)
            v = java_num(args[1])[1]
            if v == 'NaN': return dict(p, kind='nan', expr=S(0))
            return dict(p, kind='doubleNear', expr=S(0), expected=v, delta=delta)
    if cls == 'TestFunctions' and helper == 'test':
        a = re.sub(r'\s+', '', args[1])
        checks = {
            'nv->nv.isDayTimeDuration()': 'datatype(?r) = <%sdayTimeDuration>' % XSD,
            'nv->nv.isDateTime()': 'datatype(?r) = <%sdateTime>' % XSD,
            'nv->nv.getDateTime().getTimezone()>=-14*60': 'TIMEZONE(?r) >= "-PT14H"^^<%sdayTimeDuration>' % XSD,
        }
        if a in checks: return dict(p, kind='check', expr=S(0), check=checks[a])
        return dict(p, kind='sameTerm', expr=S(0), expected=nodevalue(args[1], cs))
    if cls == 'TestRegex' and helper == 'regexTest':
        fl = '' if args[2] == 'null' else ', ' + json.dumps(S(2))
        e = 'REGEX(%s, %s%s)' % (json.dumps(S(0)), json.dumps(S(1)), fl)
        return dict(p, kind='boolean', expr=e, expected=args[3])
    if cls == 'TestStringArgCompatibility':
        # checkAndGetStringLiteral is the string-literal argument check of the
        # SPARQL string functions (SPARQL 1.1 §17.4.3.1.1): STRLEN applies it.
        # checkTwoArgumentStringLiterals is argument compatibility
        # (§17.4.3.1.4): CONTAINS applies it.
        if helper == 'testArgGood': return dict(p, kind='bound', expr='STRLEN(%s)' % S(0))
        if helper == 'testArgBad': return dict(p, kind='evalError', expr='STRLEN(%s)' % S(0))
        if helper in ('test2ArgsGood', 'testNArgsGood'): return dict(p, kind='bound', expr='CONTAINS(%s, %s)' % (S(0), S(1)))
        if helper in ('test2ArgsBad', 'testNArgsBad'): return dict(p, kind='evalError', expr='CONTAINS(%s, %s)' % (S(0), S(1)))
    if cls == 'TestComparison' and helper == 'compare':
        a, b, op = S(0), S(1), args[2]
        if wrapped or op == 'CMP_INDETERMINATE':
            return dict(p, kind='evalError', expr='(%s) < (%s)' % (a, b))
        rel = {'CMP_EQUAL': '=', 'CMP_UNEQUAL': '!=', 'CMP_LESS': '<'}[op]
        return dict(p, kind='boolean', expr='(%s) %s (%s)' % (a, rel, b), expected='true')
    if cls == 'TestXSDFuncOp' and helper == 'testDateTimeCast':
        dt = re.fullmatch(r'XSDDatatype\.XSD(\w+)', args[1].strip()).group(1)
        e = '<%s%s>(%s)' % (XSD, dt, nodevalue(args[0], cs))
        if wrapped: return err(e)
        return dict(p, kind='sameTerm', expr=e, expected=nodevalue(args[2], cs))
    raise ValueError('no port rule for %s.%s' % (cls, helper))


def main():
    out = []
    for f in sorted(os.listdir(EXPR_DIR)):
        if not f.endswith('.java'): continue
        src = open(os.path.join(EXPR_DIR, f), encoding='utf-8').read()
        cs, cls = Consts(src), f[:-5]
        for ln, line in enumerate(src.split('\n'), 1):
            m = ONE.match(line)
            if not m: continue
            name, body = m.group(1), m.group(2).strip()
            rec = {'id': cls + '.' + name, 'line': ln, 'java': body}
            inner, wrapped = body.rstrip(';').strip(), None
            w = re.fullmatch(r'assertThrows\(\s*(\w+)\.class\s*,\s*\(\)\s*->\s*(.*)\)', inner)
            if w: wrapped, inner = w.group(1), w.group(2).strip().rstrip(';').strip()
            hm = re.fullmatch(r'([\w.]+)\s*\((.*)\)', inner)
            helper = hm.group(1) if hm else '?'
            if cls in TRANSFORM_CLASSES:
                rec['unported'] = 'Jena expression-transform API (ExprTransform, NodeTransform); no SPARQL result'
            elif helper in UNPORTED:
                rec['unported'] = UNPORTED[helper]
            else:
                rec['port'] = port(cls, helper, split_top(hm.group(2), ','), cs, wrapped)
            out.append(rec)
    ported = [r for r in out if 'port' in r]
    doc = {
        'source': 'Apache Jena commit a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98, '
                  'jena-arq/src/test/java/org/apache/jena/sparql/expr/<class>.java',
        'licence': 'Derived from Apache Jena, Apache License 2.0. Apache Jena: Copyright The Apache '
                   'Software Foundation. Change (Factoidal, 2026-10-26): each one-line Java test is '
                   'rewritten as a SPARQL expression and a check kind by '
                   'tools/jena-facade-study/extract.py. See NOTICE in this directory.',
        'counts': {'oneLineDeclarations': len(out), 'ported': len(ported), 'unported': len(out) - len(ported)},
        'cases': out,
    }
    with open(OUT, 'w', encoding='utf-8') as fh:
        json.dump(doc, fh, indent=1, ensure_ascii=False)
        fh.write('\n')
    print(doc['counts'])
    print(collections.Counter(r['port']['kind'] for r in ported))
    print(collections.Counter(r['unported'] for r in out if 'unported' in r))


main()
