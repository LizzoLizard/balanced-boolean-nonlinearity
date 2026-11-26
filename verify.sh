#!/bin/sh
# Check everything in this repository. Needs Lean 4.15.0 on PATH (see lean-toolchain) and python3.
set -eu
cd "$(dirname "$0")"
fail() { echo "FAIL: $*" >&2; exit 1; }

echo "== 1. Lean version"
lean --version | grep -q 'version 4\.15\.0' || fail "need Lean 4.15.0, found: $(lean --version)"
lean --version

echo "== 2. SHA-256 checksums"
if command -v sha256sum >/dev/null 2>&1; then (cd lean && sha256sum -c SHA256SUMS) || fail "checksum mismatch"
else (cd lean && shasum -a 256 -c SHA256SUMS) || fail "checksum mismatch"; fi

echo "== 3. Forbidden tokens outside comments"
for f in lean/ChallengeDefs.lean lean/Solution.lean lean/EvenBalancedBound.lean lean/EvenBalanced8Bound.lean; do
  hits=$(python3 tools/strip_comments.py "$f" | grep -n -E \
    '(^|[^A-Za-z0-9_.])(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|set_option|opaque)([^A-Za-z0-9_]|$)' || true)
  [ -z "$hits" ] || { echo "$hits"; fail "forbidden token in $f"; }
  echo "$f: clean"
done

echo "== 4. Compile (about 2 minutes in total)"
build=$(mktemp -d "${TMPDIR:-/tmp}/evenbal.XXXXXX")
trap 'rm -rf "$build"' EXIT
for m in ChallengeDefs Challenge EvenBalancedBound EvenBalanced8Bound Solution; do
  start=$(date +%s)
  LEAN_PATH="$build" lean -o "$build/$m.olean" "lean/$m.lean" > "$build/$m.log" 2>&1 \
    || { cat "$build/$m.log"; fail "$m did not compile"; }
  if [ "$m" != Challenge ] && grep -q -E 'error|declaration uses .sorry.' "$build/$m.log"; then
    cat "$build/$m.log"; fail "$m reported errors"; fi
  echo "$m: compiled in $(( $(date +%s) - start )) s"
done

echo "== 5. Comparator: Solution proves exactly the statements in Challenge"
LEAN_PATH="$build" lean/check_comparator.sh > "$build/cmp.out" 2>&1 || { cat "$build/cmp.out"; fail "comparator check failed"; }
cat "$build/cmp.out"

echo "== 6. Axioms of the theorems in the proof files"
cat > "$build/Check.lean" <<'LEAN'
import EvenBalancedBound
import EvenBalanced8Bound
#print axioms EvenBalanced8Bound.even_balanced_no_nl_ge_from8
#print axioms EvenBalanced8Bound.even_balanced_nl_le_from8
#print axioms EvenBalanced8Bound.balanced_8_no_118
#print axioms EvenBalanced8Bound.balanced_8_nl_le_116
#print axioms EvenBalanced8Bound.balanced_10_no_494
#print axioms EvenBalanced8Bound.balanced_10_nl_le_492
#print axioms EvenBalanced8Bound.sbox_even_nl_le_from8
#print axioms EvenBalanced8Bound.permutation_even_nl_le_from8
#print axioms EvenBalanced8Bound.sbox_8bit_nl_le_116
#print axioms EvenBalanced8Bound.permutation_8bit_nl_le_116
#print axioms EvenBalanced8Bound.sbox_10bit_nl_le_492
#print axioms EvenBalanced8Bound.permutation_10bit_nl_le_492
#print axioms EvenBalanced8Bound.sarkar_maitra_divisibility
#print axioms EvenBalanced8Bound.t_resilient_even_nl_le
#print axioms EvenBalanced8Bound.t_resilient_high_order_nl_le
#print axioms EvenBalancedBound.even_balanced_no_nl_ge
#print axioms EvenBalancedBound.even_balanced_nl_le
#print axioms EvenBalancedBound.balanced_10_no_494
#print axioms EvenBalancedBound.balanced_10_nl_le_492
#print axioms EvenBalancedBound.balanced_12_nl_le_2012
#print axioms EvenBalancedBound.balanced_14_nl_le_8124
#print axioms EvenBalancedBound.balanced_16_nl_le_32636
LEAN
LEAN_PATH="$build" lean "$build/Check.lean" > "$build/check.out" 2>&1 || { cat "$build/check.out"; fail "axiom check failed"; }
cat "$build/check.out"
n=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$build/check.out" || true)
[ "$n" -eq 22 ] || fail "expected 22 theorems on exactly [propext, Classical.choice, Quot.sound], got $n"

echo "== ALL CHECKS PASSED"
