#!/bin/bash
# Gate for the Lean formalisation. It passes only if all of these hold:
#  * the sources contain no `sorry`, `admit`, `native_decide`, `axiom` keyword (anywhere,
#    including one on a line of its own), `#eval`, `run_cmd`, `initialize`, `IO`, `set_option`,
#    or syntax-extension commands (`macro`, `elab`, `syntax`, `notation`, `import Lean`, ...),
#    which could redefine `#print axioms`;
#  * the library builds without errors;
#  * the gate itself (not a file in the repo) generates the `#print axioms` report for each
#    REQUIRED theorem, and each report is present exactly once;
#  * each REQUIRED theorem (with its transitive dependencies) uses only Lean's standard axioms
#    (propext, Classical.choice, Quot.sound).
# Trust boundary: the token filter is a heuristic over the project's .lean sources. The gate assumes
# the pinned toolchain, Mathlib and lake configuration are unmodified. It is not a sandbox, and it
# does not audit declarations other than the REQUIRED theorems.
# REQUIRED lists every declaration named in the accompanying paper (theorems and definitions);
# definitions may use a subset of the standard axioms.
# Lean wraps long axiom lists across several lines, so the output is flattened before parsing.
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")" || exit 1
NS="PlaneCubic"
LIB="CayleyBacharach"
REQUIRED="AtLeastThree AtLeastThree.of_infinite CardGT CommonZero ExactlyMeetIn atLeastThree_iff_card card_add_one_le card_le_seven_of_not_atLeastThree cayley_bacharach cayley_bacharach_any cayley_bacharach_classical cayley_bacharach_classical_card cayley_bacharach_classical_card8 cayley_bacharach_classical_fintype cayley_bacharach_of_no_common_factor cayley_bacharach_of_no_common_factor_any classical_conic_case classical_line_case coeffs_eq_zero_of_forall_three conic_line_lemma conic_points conic_three conics_le_one conics_le_two conics_off_line_ge_two cubic_four cubics_resid det_gram_eq_zero_iff det_gram_linMul det_gram_linMul_char_two eval evalC evalC_expand evalC_linMul evalC_smul_vec eval_expand eval_mulLin eval_smul_vec exists_conic_off_line exists_linMul_of_det_gram_eq_zero false_of_conic finrank_cubicsThrough_le_two finrank_ker_evalMap_eq_two finrank_ker_evalMap_eq_two_any finrank_ker_ge_of_conic finrank_ker_ge_of_line finrank_le_three_of_no3 general_position_of_no_common_factor gram gram_quadForm ker_evalMap_eq linMul line_comp_of_polar line_lemma line_lemma_false_zmod_two line_lemma_fintype line_points mem_span_of_eight mulLin ne_zero_of_pairwise no_common_conic_of_exact no_common_line_of_exact noncollinear_of_irreducible pappus_clean pappus_generic pappus_lines_distinct pappus_of_cayley_bacharach pascal_clean pascal_clean_det pascal_generic pascal_of_cayley_bacharach pascal_points_off_conic vanishesAt_smul_iff"
SOURCES="CayleyBacharach/*.lean CayleyBacharach.lean"
[ -e .lake/packages/mathlib ] || lake exe cache get || { echo "FAIL: could not fetch Mathlib cache"; exit 1; }
if grep -nE "\bsorry\b|\badmit\b|native_decide|\baxiom\b|#eval|\brun_cmd\b|\binitialize\b|\bIO\b|\bdebug\.|\bmacro|\belab|\bsyntax\b|\bnotation\b|\binfix|\bprefix\b|\bpostfix\b|import Lean|open Lean|\bset_option\b" $SOURCES; then
  echo "FAIL: forbidden token"; exit 1; fi
build=$(lake build $LIB 2>&1); bstatus=$?
printf '%s\n' "$build" | tail -3
[ "$bstatus" -eq 0 ] || { printf '%s\n' "$build"; echo "FAIL: build"; exit 1; }
# The `#print axioms` queries are generated here rather than read from a file in the repo.
chk=$(mktemp --suffix=.lean -p . .gatecheck_XXXX)
trap 'rm -f "$chk"' EXIT
{ echo "import $LIB"; for t in $REQUIRED; do echo "#print axioms $NS.$t"; done; } > "$chk"
out=$(lake env lean "$chk" 2>&1); status=$?
printf '%s\n' "$out"
[ "$status" -eq 0 ] || { echo "FAIL: axiom report"; exit 1; }
echo "$out" | grep -qE "(^|:)[[:space:]]*error" && { echo "FAIL: Lean reported an error"; exit 1; }
flat=$(printf '%s\n' "$out" | awk '/^'"'"'/{if(buf!="")print buf; buf=$0; next} {buf=buf" "$0} END{if(buf!="")print buf}')
reports=$(printf '%s\n' "$flat" | grep -E "depends on axioms|does not depend on any axioms")
n=0
for t in $REQUIRED; do
  c=$(printf '%s\n' "$reports" | grep -cE "^'$NS\.$t' (depends on axioms|does not depend)")
  [ "$c" -eq 1 ] || { echo "FAIL: expected one axiom report for $t, found $c"; exit 1; }
  n=$((n+1))
done
[ "$(printf '%s\n' "$reports" | grep -c .)" -eq "$n" ] || { echo "FAIL: unexpected extra reports"; exit 1; }
printf '%s\n' "$reports" | grep "depends on axioms" | grep -qv '\]' && { echo "FAIL: unterminated axiom list"; exit 1; }
bad=$(printf '%s\n' "$reports" | grep "depends on axioms" | sed 's/.*depends on axioms: *\[//; s/\].*//' \
      | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$' | sort -u \
      | grep -vE '^(propext|Classical\.choice|Quot\.sound)$')
[ -n "$bad" ] && { echo "FAIL: nonstandard axioms: $bad"; exit 1; }
echo "PASS ($n theorems, standard axioms only)"
