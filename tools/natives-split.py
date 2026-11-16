#!/usr/bin/env python3
"""Split the two large built-in dispatchers of JS/Interp.lean (`Natives.moreNative`,
`Natives.callNative`) into one definition per family of built-ins (issue 531; one-off refactor,
kept as the record of how).

Each was one `match id with` of about a hundred arms (2,078 and 1,487 lines). An arm goes, with
its text unchanged, to the definition of its family (`FAMILIES` below: by the name of the first
constructor of its pattern); that definition matches `id` again over its own arms only. The
dispatcher keeps what ran before the match (the step charge of `callNative`, the read of the
realm) and its `match id with`, with the same patterns in the same order, each arm now a call of
the family's definition. So a property of a dispatcher is proved per family (a few hundred lines
each), and the dispatcher's own lemma is a match over calls.

A family takes the realm the dispatcher read (`r`), and binds for itself the pure locals of the
old preamble that its arms use (`a0`, `a1`, `id_`, the local helpers).

usage: natives-split.py Interp.lean [--eq OUT.lean]

`--eq` also writes a module with the two definitions as they were (`moreNativeRef`,
`callNativeRef`) and the theorems that the new ones equal them (by cases on `id` and `rfl`): a
check of the refactor, not built by CI.
"""
import re
import sys

path = sys.argv[1]
eq_out = sys.argv[sys.argv.index('--eq') + 1] if '--eq' in sys.argv else None
src = open(path).read().split('\n')

# family -> (description, constructor names). Order of the definitions in the file.
FAMILIES = {
    'moreNative': [
        ('Buffers', 'ArrayBuffer `resize`, `transfer` and accessors, the DataView accessors, SharedArrayBuffer, and Atomics without waiting',
         'dataViewGetter bufferGetter bufferResize bufferTransfer sharedCtor sharedGetter sharedGrow sharedSlice atomics'),
        ('Typed', '%TypedArray%: the constructor, `from`, `of`, the accessors, the methods with Array.prototype\'s steps, `toLocaleString`, and the Uint8Array base64 and hex methods',
         'typedArrayCtor typedOf typedFrom typedGetter typedGeneric arrayToLocaleString u8Base64'),
        ('TypedMethod', 'the %TypedArray%.prototype methods that answer a typed array or work on its bytes',
         'typedMethod'),
        ('Disposable', 'SuppressedError, DisposableStack and `Iterator.prototype[@@dispose]`',
         'suppressedErrorCtor disposableStackCtor disposableStackDisposed disposableStackMethod adoptClosure iteratorDispose'),
        ('AsyncDisposable', 'AsyncDisposableStack',
         'asyncDisposableStackCtor asyncDsDisposed asyncDsSyncWrap asyncDsMethod asyncDsStep'),
        ('Iterator', 'the Iterator constructor, `Iterator.concat`, `Iterator.from` and the lazy iterator helpers',
         'iteratorCtor iteratorConcat iteratorFrom iterLazy'),
        ('IteratorZip', '`Iterator.zip` and `Iterator.zipKeyed`', 'iteratorZip'),
        ('IterEager', 'the iterator helpers that run the iterator to its end (`reduce`, `toArray`, `forEach`, `some`, `every`, `find`)',
         'iterEager'),
        ('IterHelper', '`next` and `return` of the iterator helper objects', 'helperNext'),
        ('Object', 'Function, Error and Object additions (`@@hasInstance`, `Error.isError`, `stack`, AggregateError, `Object.hasOwn`, `__proto__`, `Proxy.revocable`, the Function constructors) and the host\'s realm hooks',
         'fnHasInstance errorIsError errorStack aggregateErrorCtor namedGetterSet speciesGetter objectHasOwn protoAccessor gcNoop realmTake dynFunction proxyRevocable proxyRevoke'),
        ('Date', 'Temporal and the Date methods', 'temporal dateUTC dateParse dateMethod'),
        ('Promise', '`Promise.try`, `Promise.withResolvers`, the capability executor, thenable functions and `import()`',
         'promiseTry promiseWithResolvers capabilityExecutor promiseThenableFn dynImport'),
        ('String', 'String, RegExp, Number and Symbol additions (the HTML methods, `compile`, `RegExp.escape`, `toExponential`, `toPrecision`, `localeCompare`, `String.raw`, `Symbol.for`, `isWellFormed`)',
         'regexpSym stringHtml regexpCompile regexpEscape numberToExponential stringLocaleCompare stringRaw symbolFor stringIsWellFormed'),
        ('Set', 'the Set methods of two sets and the collection methods shared by Map, Set and their weak kinds',
         'collMethod setMethod'),
        ('Weak', 'WeakRef, FinalizationRegistry, `groupBy` and the Map upsert methods',
         'groupBy weakRefCtor weakRefDeref finRegCtor finRegMethod mapUpsert'),
        ('Array', 'the Array methods that copy (`toReversed`, `toSorted`, `toSpliced`, `with`) and their kin', 'arrayMethod'),
        ('Clone', 'structured clone and classic scripts, for workers', 'cloneSerialize cloneDeserialize classicScript'),
        ('Web', 'streams and URLPattern', 'streams urlPattern'),
        ('AsyncIter', '`for await` and the async-from-sync iterator', 'forAwait asyncFromSync'),
        ('FromAsync', '`Array.fromAsync`', 'arrayFromAsync fromAsyncStep'),
    ],
    'callNative': [
        ('Global', 'the global functions, `eval`, `%ThrowTypeError%` and `Date.now`',
         'print isNaN isFinite parseInt parseFloat eval throwTypeError dateNow'),
        ('ObjectStatic', 'the Object constructor and its static methods',
         'objectCtor objectKeys objectGetOwnPropertyNames objectGetPrototypeOf objectSetPrototypeOf objectCreate objectDefineProperty objectGetOwnPropertyDescriptor objectIs objectFreeze objectIsFrozen objectPreventExtensions objectIsExtensible objectGetOwnPropertySymbols objectAssign objectEntries objectDefineProperties objectSeal objectIsSealed objectGetOwnPropertyDescriptors objectFromEntries'),
        ('ObjectProto', 'Object.prototype and Function',
         'objectProtoHasOwnProperty objectProtoPropertyIsEnumerable objectProtoDefineGetter objectProtoLookupGetter objectProtoIsPrototypeOf objectProtoToString objectProtoToLocaleString objectProtoValueOf functionCtor functionProto functionProtoCall functionProtoApply functionProtoBind functionProtoToString'),
        ('ArrayEdit', 'the Array constructor and the methods that change the array',
         'arrayCtor arrayIsArray arrayPush arrayPop arrayShift arrayUnshift arraySlice arraySplice arrayReverse arrayFill arraySort'),
        ('ArrayRead', 'the Array methods that read the array, and its iterators',
         'arrayJoin arrayIndexOf arrayLastIndexOf arrayConcat arrayMap arrayReduce arrayValues arrayFlat arrayAt arrayFindLast'),
        ('ArrayFrom', '`Array.from` and `Array.of`', 'arrayFrom arrayOf'),
        ('String', 'the String constructor and the String methods kept here',
         'stringCtor stringFromCharCode stringToString stringIterator stringAt stringPadStart stringCodePointAt stringTrimStart stringReplace stringFromCodePoint stringSplit stringMatch stringMatchAll'),
        ('Number', 'Number, Boolean, Math and BigInt',
         'numberCtor numberValueOf numberIsInteger booleanCtor booleanToString numberIsFinite numberIsNaN numberIsSafeInteger math1 mathHypot mathImul mathClz32 bigintCtor bigintAsN bigintToString'),
        ('Error', 'Error, `JSON.stringify` and Symbol',
         'errorCtor errorToString jsonStringify symbolCtor symbolToString'),
        ('Generator', 'the built-in iterators\' `next`, generators and async functions',
         'iterNext iterSelf agenNext agenResume asyncResume genNext'),
        ('Promise', 'the Promise constructor, its prototype methods, `resolve`, `reject` and the jobs',
         'promiseCtor promiseInitOn promiseResolveFn promiseThen promiseCatch promiseFinally promiseFinallyF promiseValueThunk promiseThrower promiseResolveStatic promiseRejectStatic promiseReactionJob promiseThenableJob'),
        ('PromiseAll', 'the Promise combinators (`all`, `allSettled`, `any`, `race`, the keyed ones) and their element functions',
         'promiseAll promiseKeyed promiseAllElement'),
        ('Map', 'Map, Set and their weak kinds', 'mapCtor mapGet'),
        ('Reflect', 'Reflect', 'reflect'),
    ],
}
# arms of callNative that stay in the dispatcher: they already are calls of other definitions
KEEP = {'regexpCtor', 'x', '_'}
# The end of a long arm as a definition of its own: (constructor of the arm, the first line of
# the part that moves, the definition's name, its parameters after `core` and `r`, its doc).
# The arm keeps what comes before and ends with the call. (`setMethod`: the walk of the whole
# arm took 16,000 steps and 3.9 GB; the checks before `mine` and the methods apart take far less.)
TAILS = {
    'setMethod': ('      let mine : Array Value := es.filterMap (·.map (·.1))', 'setMethodRun',
                  '(k : Nat) (sid : Nat) (es : Array (Option (Value × Value))) (a0 : Value) (has : Value) (keys : Value) (otherSize : Float)',
                  'The Set methods of two sets (§24.2.4 to §24.2.4.20: 0 `union`, 1 `intersection`, 2 `difference`, 3 `symmetricDifference`, 4 `isSubsetOf`, 5 `isSupersetOf`, else `isDisjointFrom`), after the receiver `sid` (entries `es`) and the argument\'s set record (`a0`, its `size`, `has` and `keys`) are read.'),
}


def func(name):
    i = next(k for k, l in enumerate(src) if l.startswith(f'def {name} (core : CoreFn H)'))
    j = i + 1
    while not (src[j].startswith('def ') or src[j].startswith('/--') or src[j].startswith('end ')):
        j += 1
    while src[j - 1].strip() == '':
        j -= 1
    return i, j


def parse(name):
    """(def line, match line, end, arms); an arm is (comments before it, pattern lines, body lines)."""
    i, j = func(name)
    m = next(k for k in range(i, j) if src[k] == '    match id with')
    arms = []
    k = m + 1
    pend = []
    while k < j:
        l = src[k]
        if l.startswith('    --'):
            if '==== end' not in l:   # the end of a section of arms, not a comment on the next
                pend.append(l)
            k += 1
            continue
        assert l.startswith('    | '), (k + 1, l)
        hdr = [l]
        while '=>' not in hdr[-1]:
            k += 1
            assert src[k].startswith('    | '), (k + 1, src[k])
            hdr.append(src[k])
        k += 1
        body = []
        while k < j and not src[k].startswith('    | ') and not src[k].startswith('    --'):
            assert src[k].strip() == '' or src[k].startswith('      '), (k + 1, src[k])
            body.append(src[k])
            k += 1
        arms.append((pend, hdr, body))
        pend = []
    assert not pend
    return i, m, j, arms


def first_ctor(hdr):
    m = re.match(r'    \| \(\.x \(?\.(\w+)', hdr[0]) or re.match(r'    \| \.(\w+)', hdr[0])
    if m:
        return m.group(1)
    assert hdr[0].startswith('    | _ =>'), hdr
    return '_'


def preamble(i, m):
    """The statements between the signature and `match id with`: (name, lines)."""
    stmts = []
    pend = []
    for l in src[i + 1:m]:
        if l.startswith('    --'):
            pend.append(l)
        elif l.startswith('    ') and not l.startswith('     '):
            mm = re.match(r'    let (\w+)', l)
            stmts.append([mm.group(1) if mm else l.split()[0], pend + [l]])
            pend = []
        else:
            assert not pend
            stmts[-1][1].append(l)
    return stmts


def uses(name, text):
    return re.search(r'(?<![\w.])' + re.escape(name) + r'(?![\w])', text) is not None


def blank_binders(pat):
    """A pattern with its variables as `_` (the dispatcher's arm does not use them)."""
    return re.sub(r'(?<![.\w])(?!true\b|false\b)[a-z]\w*', '_', pat)


SIG = '(core : CoreFn H) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value'
FSIG = '(core : CoreFn H) (r : Realm) (id : Native) (thisV : Value) (args : Array Value) (newTarget : Option Value) : M Value'
# preamble statements that stay in the dispatcher (they run once, before the match)
DISPATCH_ONLY = {'recvCost', 'argsCost', 'charge', 'r'}

ref_text = {}
fam_names = {}
for name in ['callNative', 'moreNative']:   # the later one first: line numbers above stay valid
    i, m, j, arms = parse(name)
    d0 = i
    while not src[d0 - 1].startswith('/--'):
        d0 -= 1
    d0 -= 1
    ref_text[name] = src[d0:j]
    pre = preamble(i, m)
    assert [n for n, _ in pre if n in DISPATCH_ONLY][-1] == 'r'
    fams = FAMILIES[name]
    of = {}
    for fam, _, cs in fams:
        for c in cs.split():
            assert c not in of, c
            of[c] = fam
    members = {fam: [] for fam, _, _ in fams}
    tails = {}
    disp = []
    for pend, hdr, body in arms:
        c = first_ctor(hdr)
        if c in KEEP and (name == 'callNative' or c == '_'):
            disp += hdr + body
            continue
        fam = of[c]
        if c in TAILS:
            mark, tname, tparams, tdoc = TAILS[c]
            k = body.index(mark)
            tail = [l[2:] if l.startswith('  ') else l for l in body[k:]]
            targs = ' '.join(re.findall(r'\((\w+) :', tparams))
            tails.setdefault(fam, []).extend(
                [f'/-- {tdoc} -/', f'def {tname} (core : CoreFn H) (r : Realm) {tparams} : M Value := do'] + tail + [''])
            body = body[:k] + [f'      {tname} core r {targs}']
        members[fam].append((pend, hdr, body))
        call = f'{name}{fam} core r id thisV args newTarget'
        h = [blank_binders(x) for x in hdr]
        h[-1] = h[-1][:h[-1].index('=>')] + '=> ' + call
        disp += h
    out = []
    fam_names[name] = []
    for fam, desc, _ in fams:
        ms = members[fam]
        assert ms, fam
        text = '\n'.join('\n'.join(p + h + b) for p, h, b in ms)
        # the pure locals of the old preamble this family uses (a helper may use another)
        need = set()
        changed = True
        while changed:
            changed = False
            for n, ls in pre:
                if n in DISPATCH_ONLY or n in need:
                    continue
                if uses(n, text) or any(uses(n, '\n'.join(l2)) for n2, l2 in pre if n2 in need):
                    need.add(n)
                    changed = True
        out += tails.get(fam, [])
        out.append(f'/-- Built-ins of `{name}`: {desc}. `r` is the realm `{name}` read. -/')
        out.append(f'def {name}{fam} {FSIG} := do')
        for n, ls in pre:
            if n in need:
                out += ls
        out.append('    match id with')
        for p, h, b in ms:
            out += p + h + b
        out.append('    | _ => throwErr .type "not a function"')
        out.append('')
        fam_names[name].append(f'{name}{fam}')
    new = out + src[d0:i + 1]
    for n, ls in pre:
        if n in DISPATCH_ONLY:
            new += ls
    new.append('    match id with')
    new += disp
    src[d0:j] = new

# the section's description, with where a built-in goes now
text = '\n'.join(src)
old_doc = '''`callNative`, `extraNative` and `moreNative` (about 4,000 lines) call back into the evaluator
through one dispatcher, `CoreFn`: a request (`CoreOp`, one constructor per function of the block
they use) and its answer (`CoreOp.Res`). Out of the block they are plain definitions, so Lean
makes no structural-recursion equation lemmas for them (those of the block took minutes and
gigabytes), and a property of the block is proved for them once, from the same property of the
dispatcher (`JS/FuelMono.lean`). Inside the block, `coreRun n` answers requests at fuel `n`. -/'''
new_doc = old_doc[:-3] + '''

`callNative` and `moreNative` are each a `match id with` over calls of one definition per family
of built-ins (`callNativeObjectStatic`, `moreNativeTyped`, ...: `tools/natives-split.py`), so
that a property is proved family by family (a few hundred lines each; the two as single
definitions of 1,500 and 2,100 lines were beyond a 6 GB proof check). A new built-in is an arm
in its family's definition and an arm of the dispatcher that calls the family; a new family is a
definition before the dispatcher, with the same parameters, and `tools/fuelmono-natives.py`
writes its fuel-monotonicity lemma (`JS/FuelMonoNatives_*.lean`). -/'''
assert text.count(old_doc) == 1
text = text.replace(old_doc, new_doc)
open(path, 'w').write(text)

if eq_out:
    w = ['import L4Factoidal.JS.Interp', '',
         '/-! The built-in dispatchers `Natives.moreNative` and `Natives.callNative` as they were before',
         'they were split by family (issue 531, `tools/natives-split.py --eq`), and the theorems that the',
         'split ones equal them. A check of the refactor; generated, not built by CI. -/', '',
         'set_option maxHeartbeats 0', 'set_option linter.unusedVariables false',
         'set_option linter.constructorNameAsVariable false', '',
         'namespace L4Factoidal.JS', '', 'variable {H : Type}', 'set_option hygiene false in',
         'local notation "M" => JSM H', '', 'namespace Natives', '']
    for name in ['moreNative', 'callNative']:
        t = '\n'.join(ref_text[name])
        t = t.replace(f'def {name} (core', f'def {name}Ref (core', 1)
        w += [t, '']
    w += ['end Natives', '']
    cases_nat = ('rcases k with _|_|_|_|_|_|_|_|_|k <;> rfl')
    for name in ['moreNative', 'callNative']:
        w += [f'theorem Natives.{name}_eq_ref (core : CoreFn H) (id : Native) (thisV : Value) (args : Array Value)',
              f'    (nt : Option Value) : Natives.{name} core id thisV args nt = Natives.{name}Ref core id thisV args nt := by',
              '  cases id with',
              '  | x op =>',
              '    cases op with',
              '    | errorStack b => cases b <;> rfl',
              '    | protoAccessor b => cases b <;> rfl',
              '    | iterEager k => ' + cases_nat,
              '    | forAwait k => ' + cases_nat,
              '    | asyncFromSync k => ' + cases_nat,
              '    | _ => rfl',
              '  | _ => rfl', '']
        if name == 'callNative':
            # the one arm with a local recursive function (`let rec walk`): its copies in the two
            # definitions are equal by induction, not by unfolding
            k = len(w) - 2
            w[k:k] = ['  | objectProtoIsPrototypeOf =>',
                      '    have hw : ∀ (h : HeapOf H) (me k : Nat) (v : Value),',
                      '        Natives.callNativeObjectProto.walk me h k v = Natives.callNativeRef.walk me h k v := by',
                      '      intro h me k',
                      '      induction k with',
                      '      | zero => intro v; rfl',
                      '      | succ k ih =>',
                      '        intro v',
                      '        cases v <;> first | rfl | skip',
                      '        rename_i o',
                      '        show (match (h.obj o).proto with | .obj q => q == me || Natives.callNativeObjectProto.walk me h k (.obj q) | _ => false)',
                      '          = (match (h.obj o).proto with | .obj q => q == me || Natives.callNativeRef.walk me h k (.obj q) | _ => false)',
                      '        split <;> simp [ih]',
                      '    have hw\' : @Natives.callNativeObjectProto.walk H = @Natives.callNativeRef.walk H := by',
                      '      funext me h k v; exact hw h me k v',
                      '    show Natives.callNative core .objectProtoIsPrototypeOf thisV args nt = _',
                      '    dsimp only [Natives.callNative, Natives.callNativeRef, Natives.callNativeObjectProto]',
                      '    rw [hw\']', '    rfl']
    w += ['end L4Factoidal.JS', '']
    open(eq_out, 'w').write('\n'.join(w))

for name in ['moreNative', 'callNative']:
    print(name, len(fam_names[name]), 'families:', ' '.join(fam_names[name]))
