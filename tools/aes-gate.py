#!/usr/bin/env python3
"""AES gate: the tree holds no software AES, and AES has exactly the entry points we name.

Rule and reasons: skills/aes-hardware-only/SKILL.md. In short: the ordinary portable AES looks
its S-box or T-tables up at an index that depends on the key, which leaks the key through cache
timing. The only AES we ship is HACL*'s Vale assembly, which uses the CPU's AES instructions, and
it is refused where the CPU has none (theorems in L4Factoidal/Crypto/AesGcmNative.lean).

What the gate checks, on every tracked file (`git ls-files`):

  1. tables: no file holds the AES S-box, the inverse S-box or the first T-table, as numbers in
     source text (hex or decimal, any separators), as a hex string, or as raw bytes. A table
     implementation cannot exist without one of them written down.
  2. round functions: no code file names two or more of the round functions of FIPS 197
     (SubBytes, ShiftRows, MixColumns, AddRoundKey, KeyExpansion and their inverses). This
     catches an implementation that computes its S-box at run time.
  3. entry points: the `@[extern]` names in Lean that mention AES, and the code files whose path
     mentions AES, are exactly the ones listed below.

`--binary FILE...` runs check 1 (raw bytes) on built libraries or Wasm modules instead.

Exceptions go in tools/aes-gate-allow.txt, one per line: `<check> <path>  # reason`. A reason is
required. Test vectors and vendored test suites are data, and are named there by directory.

What the gate cannot show: that a determined author has not hidden an AES some other way, or that
the linked assembly runs the AES instructions. The first is for review; the second rests on HACL*.

Exit 0 when clean, 1 with one line per finding otherwise.  Usage:
  python3 tools/aes-gate.py            # the tree
  python3 tools/aes-gate.py --binary libweb-render.so web-render.wasm
  python3 tools/aes-gate.py --self-test
"""
import os
import re
import subprocess
import sys

# First eight bytes of each table are enough: none of them occurs by chance in 8 ordered values.
SBOX = [0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5]
INV_SBOX = [0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38]
# T-table Te0 = (2*S, S, S, 3*S): first two words, big-endian and little-endian.
TE0_BE = [0xC66363A5, 0xF87C7C84]
TE0_LE = [0xA56363C6, 0x847C7CF8]

SEP = rb"[^0-9A-Za-z]{1,8}"


def _num_seq(values, width):
    """A regex for the values as hex (0x.. or bare, zero-padded to width) or decimal tokens."""
    suffix = rb"(?:[uUlL]{1,3})?"  # C integer suffixes
    sep = suffix + SEP
    hexes = sep.join((rb"(?:0[xX])?0*" + (b"%0*x" % (width, v))) for v in values)
    hexes_u = sep.join((rb"(?:0[xX])?0*" + (b"%0*X" % (width, v))) for v in values)
    decs = sep.join(b"%d" % v for v in values)
    return [rb"(?<![0-9A-Za-z])" + hexes + suffix + rb"(?![0-9A-Za-z])",
            rb"(?<![0-9A-Za-z])" + hexes_u + suffix + rb"(?![0-9A-Za-z])",
            rb"(?<![0-9A-Za-z])" + decs + suffix + rb"(?![0-9A-Za-z])"]


def _patterns():
    pats = []
    for name, vals, width in (("S-box", SBOX, 2), ("inverse S-box", INV_SBOX, 2)):
        raw = bytes(vals)
        pats.append((name + " (raw bytes)", re.compile(re.escape(raw))))
        pats.append((name + " (hex string)", re.compile(raw.hex().encode(), re.I)))
        for p in _num_seq(vals, width):
            pats.append((name + " (numbers)", re.compile(p)))
    for name, vals in (("T-table", TE0_BE), ("T-table", TE0_LE)):
        raw = b"".join(v.to_bytes(4, "big") for v in vals)
        pats.append((name + " (raw bytes)", re.compile(re.escape(raw))))
        for p in _num_seq(vals, 8):
            pats.append((name + " (numbers)", re.compile(p)))
    return pats


PATTERNS = _patterns()

CODE_EXT = (".lean", ".c", ".h", ".cc", ".cpp", ".s", ".S", ".asm", ".js", ".mjs", ".cjs", ".ts",
            ".py", ".ml", ".mli", ".fst", ".fsti", ".rs", ".go", ".zig", ".wat", ".wgsl", ".sh")

ROUND_FN = re.compile(
    rb"(?i)(?<![A-Za-z])(inv_?)?(sub_?bytes|shift_?rows|mix_?columns?|add_?round_?key|"
    rb"key_?expansion|aes_?key_?schedule)(?![a-z])")



def round_functions(data):
    """The distinct round-function names in a file, normalised. One alone is a coincidence
    (`subbytes` is a common name for a slice of bytes); an AES implementation has several."""
    return sorted({re.sub(rb"[_]", b"", m.group(0).lower()).decode() for m in ROUND_FN.finditer(data)})


# The whole of AES in this tree. Adding a line here is a change of crypto policy.
ENTRY_FILES = {
    "formal/lean4/L4Factoidal/Crypto/AesGcmNative.lean",  # the three externs and the theorems
    "formal/lean4/ffi/hacl_aesgcm.c",                     # the shim over EverCrypt's AEAD
    "third_party/hacl/vale/src/aesgcm-x86_64-darwin.S",   # HACL* Vale, AES-NI
    "third_party/hacl/vale/src/aesgcm-x86_64-linux.S",    # HACL* Vale, AES-NI
}
ENTRY_EXTERNS = {"l4_hacl_aesgcm_available", "l4_hacl_aesgcm_encrypt", "l4_hacl_aesgcm_decrypt"}
EXTERN = re.compile(rb'@\[\s*extern\s+"([^"]+)"')


def load_allow(root):
    allow = {}
    path = os.path.join(root, "tools", "aes-gate-allow.txt")
    if not os.path.exists(path):
        return allow
    for n, line in enumerate(open(path, encoding="utf-8"), 1):
        body, _, reason = line.partition("#")
        parts = body.split()
        if not parts:
            continue
        if len(parts) != 2 or not reason.strip():
            sys.exit(f"tools/aes-gate-allow.txt:{n}: want '<check> <path>  # reason'")
        allow.setdefault(parts[0], []).append(parts[1])
    return allow


def allowed(allow, check, path):
    return any(path == p or (p.endswith("/") and path.startswith(p)) for p in allow.get(check, []))


# One cheap pass decides whether the exact patterns need to run: each table, in every form above,
# contains one of these fragments (its second and third values, or a whole first word).
PREFILTER = re.compile(
    rb"(?i)7c(?:[ul]{1,3})?[^0-9a-z]{1,8}(?:0x)?0*77|124[^0-9a-z]{1,8}119|637c777b|"
    rb"09(?:[ul]{1,3})?[^0-9a-z]{1,8}(?:0x)?0*6a|(?<![0-9])9[^0-9a-z]{1,8}106|52096ad5|"
    rb"c66363a5|a56363c6")
RAW = [bytes(SBOX), bytes(INV_SBOX), (0xC66363A5).to_bytes(4, "big") + (0xF87C7C84).to_bytes(4, "big"),
       (0xA56363C6).to_bytes(4, "big") + (0x847C7CF8).to_bytes(4, "big")]


def scan_tables(data):
    if not PREFILTER.search(data) and not any(r in data for r in RAW):
        return []
    return sorted({name for name, pat in PATTERNS if pat.search(data)})


def scan_tree(root):
    allow = load_allow(root)
    files = subprocess.run(["git", "-C", root, "ls-files", "-z"], check=True,
                           capture_output=True).stdout.split(b"\0")
    findings = []
    for raw in files:
        if not raw:
            continue
        rel = raw.decode("utf-8", "surrogateescape")
        full = os.path.join(root, rel)
        if os.path.islink(full) or not os.path.isfile(full):
            continue
        if rel in ("tools/aes-gate.py", "tools/aes-gate-allow.txt"):
            continue
        try:
            data = open(full, "rb").read()
        except OSError:
            continue
        is_code = rel.endswith(CODE_EXT)
        if not allowed(allow, "tables", rel):
            for name in scan_tables(data):
                findings.append(f"tables: {rel}: holds the AES {name}")
        if is_code and not allowed(allow, "round-functions", rel) and rel not in ENTRY_FILES:
            names = round_functions(data)
            if len(names) >= 2:
                findings.append(f"round-functions: {rel}: names {', '.join(names)} "
                                f"(round functions of FIPS 197: an AES implementation?)")
        if rel.endswith(".lean"):
            for m in EXTERN.finditer(data):
                sym = m.group(1).decode("utf-8", "replace")
                if ("aes" in sym.lower() and (sym not in ENTRY_EXTERNS or rel not in ENTRY_FILES)
                        and not allowed(allow, "entry-points", rel)):
                    line = data.count(b"\n", 0, m.start()) + 1
                    findings.append(f"entry-points: {rel}:{line}: extern {sym} is not one of "
                                    f"the three AES externs of Crypto/AesGcmNative.lean")
        if (is_code and "aes" in os.path.basename(rel).lower() and rel not in ENTRY_FILES
                and not allowed(allow, "entry-points", rel)):
            findings.append(f"entry-points: {rel}: a code file named for AES that is not in "
                            f"the list of AES entry points")
    missing = sorted(f for f in ENTRY_FILES if not os.path.isfile(os.path.join(root, f)))
    for f in missing:
        findings.append(f"entry-points: {f}: listed as an AES entry point but not in the tree")
    return findings


def scan_binaries(paths):
    findings = []
    for p in paths:
        data = open(p, "rb").read()
        for name in scan_tables(data):
            findings.append(f"tables: {p}: holds the AES {name}")
    return findings


def self_test():
    sbox_c = b"static const uint8_t sbox[256] = {0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30};"
    sbox_lean = b"def sbox : Array UInt8 := #[99, 124, 119, 123, 242, 107, 111, 197, 48]"
    sbox_hex = b'const S = "637C777BF26B6FC53001672BFED7AB76";'
    te0 = b"static const u32 Te0[256] = { 0xc66363a5U, 0xf87c7c84U, 0xee777799U };"
    inv = b"[0x52,0x09,0x6a,0xd5,0x30,0x36,0xa5,0x38]"
    clean = b"let xs := #[63, 124, 119]; -- 0x63 0x7c only two of them\nvpaesenc %xmm1, %xmm2"
    assert scan_tables(sbox_c) and scan_tables(sbox_lean) and scan_tables(sbox_hex)
    assert scan_tables(te0) and scan_tables(inv) and scan_tables(bytes(SBOX) + b"\x30")
    assert not scan_tables(clean)
    assert round_functions(b"def subBytes (s : State) := s\ndef mixColumns (s : State) := s") == \
        ["mixcolumns", "subbytes"]
    assert len(round_functions(b"void AddRoundKey(uint8_t *s); void inv_mix_columns(void);")) == 2
    assert round_functions(b"let subbytes b i n = Bytes.sub b i n") == ["subbytes"]
    assert round_functions(b"let submitBytes := 3") == []
    print("aes-gate self-test: ok")


def main(argv):
    if "--self-test" in argv:
        self_test()
        return 0
    if "--binary" in argv:
        paths = argv[argv.index("--binary") + 1:]
        if not paths:
            sys.exit("aes-gate: --binary needs files")
        findings = scan_binaries(paths)
        what = f"{len(paths)} binaries"
    else:
        root = subprocess.run(["git", "rev-parse", "--show-toplevel"], check=True,
                              capture_output=True, text=True,
                              cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
        findings = scan_tree(root)
        what = "the tree"
    for f in findings:
        print(f)
    print(f"aes-gate: {len(findings)} findings in {what}"
          + ("" if findings else " (no software AES; AES entry points as listed)"))
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
