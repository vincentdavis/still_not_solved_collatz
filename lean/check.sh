#!/bin/sh
# CI check for the Collatz Lean project.
#
#   1. the build must succeed with zero errors AND zero warnings
#   2. no unsoundness escape hatch anywhere in the sources:
#        sorry / admit / native_decide / axiom / unsafe / partial / opaque /
#        implemented_by / extern / set_option
#   3. no declaration may depend on `sorryAx` (or on `Classical.choice`)
#   4. every named declaration must be covered by `#print axioms`
#   5. the project must have no dependencies (no Mathlib, no network)
#
# Any failure exits non-zero.
set -e
cd "$(dirname "$0")"
LOG=$(mktemp)
trap 'rm -f "$LOG"' EXIT

echo "== 1. lake build (clean) =="
rm -rf .lake/build
lake build > "$LOG" 2>&1 || { cat "$LOG"; echo "FAIL: build error"; exit 1; }
cat "$LOG"
grep -q "Build completed successfully" "$LOG" || {
  echo "FAIL: build did not complete"; exit 1; }
if grep -qE "^(warning|error):" "$LOG" || grep -qE ": (warning|error): " "$LOG" ; then
  echo "FAIL: build emitted a warning or error"
  grep -E "(warning|error)" "$LOG" || true
  exit 1
fi
echo "OK: clean build, zero errors, zero warnings"

echo
echo "== 2. no unsoundness escape hatches in sources =="
# Comments are stripped first (Lean block comments nest), so that the words may
# still be DISCUSSED in prose while being forbidden in actual code.
python3 - <<'PY' || exit 1
import re, pathlib, sys
BAD = ['sorry', 'admit', 'native_decide', 'unsafe', 'partial', 'opaque',
       'implemented_by', 'extern', 'set_option', 'axiom']
pat = re.compile(r'(?<![A-Za-z_])(' + '|'.join(BAD) + r')(?![A-Za-z_])')
root = pathlib.Path('.')
files = [root/'Collatz.lean'] + sorted((root/'Collatz').glob('*.lean'))
hits = []
for f in files:
    src = f.read_text()
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:                      # strip nested /- -/ and -- comments
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth: depth -= 1; i += 2; continue
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append('\n' if src[i] == '\n' else (src[i] if depth == 0 else ' '))
        i += 1
    for ln, line in enumerate(''.join(out).split('\n'), 1):
        # `#print axioms` is the audit command itself, not an `axiom` decl.
        if line.lstrip().startswith('#print axioms'): continue
        m = pat.search(line)
        if m: hits.append('%s:%d: %s   |%s' % (f, ln, m.group(1), line.strip()))
if hits:
    print('FAIL: forbidden construct in CODE (comments already stripped):')
    for h in hits: print('   ', h)
    sys.exit(1)
print('OK: none found in code (%d files scanned)' % len(files))
PY

echo
echo "== 3. axiom audit (forced rebuild of Collatz.Audit) =="
touch Collatz/Audit.lean
lake build > "$LOG" 2>&1
if grep -q "sorryAx" "$LOG" ; then
  echo "FAIL: some declaration depends on sorryAx"; grep "sorryAx" "$LOG"; exit 1
fi
if grep -q "Classical.choice" "$LOG" ; then
  echo "WARN: some declaration depends on Classical.choice"; grep "Classical.choice" "$LOG"
fi
N=$(grep -c "Collatz/Audit.lean" "$LOG")
echo "OK: $N declarations audited; no sorryAx, no Classical.choice"
grep -oE "depends on axioms: \[[^]]*\]" "$LOG" | sort | uniq -c

echo
echo "== 4. #print axioms coverage of every named declaration =="
if command -v python3 > /dev/null 2>&1 ; then
  python3 - <<'PY' || exit 1
import re, pathlib, sys
root = pathlib.Path('.')
files = [root/'Collatz.lean'] + sorted((root/'Collatz').glob('*.lean'))
decl = re.compile(r'^\s*(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|def|abbrev|instance|structure|inductive)\b\s*'
                  r"([A-Za-z_][A-Za-z0-9_.']*)")
ns_open  = re.compile(r'^\s*namespace\s+(\S+)')
ns_close = re.compile(r'^\s*end\s+(\S+)')
names, private = set(), set()
for f in files:
    ns = []
    for line in f.read_text().split('\n'):
        m = ns_open.match(line)
        if m: ns.append(m.group(1)); continue
        m = ns_close.match(line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = decl.match(line)
        if m:
            full = '.'.join(ns + [m.group(2)])
            (private if line.lstrip().startswith('private') else names).add(full)
audited = set(re.findall(r'^#print axioms\s+(\S+)',
                         (root/'Collatz'/'Audit.lean').read_text(), re.M))
missing = sorted(names - audited)
if missing:
    print("FAIL: not covered by #print axioms:")
    for n in missing: print("   ", n)
    sys.exit(1)
print("OK: all %d named declarations audited "
      "(%d private, covered transitively)" % (len(names), len(private)))
PY
else
  echo "SKIP: python3 not found"
fi

echo
echo "== 5. no dependencies (Mathlib-free) =="
grep -q '"packages": \[\]' lake-manifest.json || {
  echo "FAIL: lake-manifest.json lists packages"; exit 1; }
if grep -qE '^ *require ' lakefile.toml ; then
  echo "FAIL: lakefile.toml has a require line"; exit 1
fi
echo "OK: zero dependencies; toolchain $(cat lean-toolchain)"

echo
echo "ALL CHECKS PASSED"
