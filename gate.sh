#!/bin/sh
# gate.sh: the whole test suite. Every law is checked by the compiler, so
# the gate only has to (1) check each module standalone, (2) run every
# example on the interpreter and the native lane against its #| block,
# and (3) refuse a module def that would silently shadow Base.
#
#   ./gate.sh                   # uses `bend` on PATH
#   BEND="bun path/to/bend2/main.ts" ./gate.sh   # a source checkout
set -u
BEND=${BEND:-bend}
cd "$(dirname "$0")"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
fail=0
say() { printf '%-28s %s\n' "$1" "$2"; }

echo "checker: $($BEND version 2>&1 | head -1)"

# 1. every module and app checks on its own
for f in src/*.bend src/*/*.bend apps/*.bend; do
  if $BEND "$f" --check-only 2>&1 | grep -q '^All terms check\.$'; then
    say "$f" ok
  else
    say "$f" FAIL; $BEND "$f" --check-only 2>&1 | head -12; fail=1
  fi
done

# 2. every example and app with a #| block, on both lanes, against it
for ex in $(grep -l '^#|' examples/*.bend apps/*.bend); do
  name=$(basename "$ex" .bend)
  sed -n 's/^#|//p' "$ex" > "$tmp/want"
  $BEND "$ex" 2>&1 | grep -v 'is available' > "$tmp/got"
  if diff -u "$tmp/want" "$tmp/got" > "$tmp/diff"; then say "$name (interpreter)" ok
  else say "$name (interpreter)" FAIL; cat "$tmp/diff"; fail=1; fi
  if $BEND "$ex" -o "$tmp/$name" > "$tmp/build" 2>&1 && "$tmp/$name" > "$tmp/got_c" 2>&1 \
     && diff -u "$tmp/want" "$tmp/got_c" > "$tmp/diff_c"; then say "$name (native)" ok
  else say "$name (native)" FAIL; cat "$tmp/build" "$tmp/diff_c" 2>/dev/null | head -20; fail=1; fi
done

# 3. no shadowing. A module imported under a Base name (as Nat, List, U32)
# silently WINS over Base for any name both define: probed 2026-09-23, a
# module def ge_refl made Nat.ge_refl return the module's value with no
# warning. So if Base ever ships one of our names, fail here and delete
# ours rather than let importers get a different definition than Base's.
for f in src/*.bend src/*/*.bend; do
  alias=$(sed -En 's/^#   import \.\/[a-z0-9]+\.bend as ([A-Za-z0-9]+).*/\1/p' "$f" | head -1)
  [ -n "$alias" ] || { say "$f" "FAIL (no '#   import ./x.bend as A' header)"; fail=1; continue; }
  names=$(sed -En 's/^(def|law|type) ([A-Za-z_][A-Za-z0-9_.]*).*/\2/p' "$f" | sort -u)
  [ -n "$names" ] || { say "$f" "FAIL (found no names: the check would pass vacuously)"; fail=1; }
  for name in $names; do
    if ! $BEND base "$alias.$name" 2>&1 | grep -q 'Base has no'; then
      say "$f" "FAIL: $alias.$name shadows Base"; fail=1
    fi
  done
done
[ $fail -eq 0 ] && say "no Base shadowing" ok

[ $fail -eq 0 ] && echo "GATE: PASS" || echo "GATE: FAIL"
exit $fail
