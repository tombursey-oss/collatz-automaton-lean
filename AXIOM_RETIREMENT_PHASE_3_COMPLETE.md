# Axiom Retirement Phase 3: Drift Totality

## Session Summary

Successfully retired the `mean_drift_defined_for_all` axiom by proving it constructively.

**Key insight:** `drift_of_edge` always returns `some`—it never fails—so the axiom follows by simple case analysis.

## The Proof

### Axiom Statement (Retired)
```lean
axiom mean_drift_defined_for_all (es : List ExpandedEdge) : (mean_drift_of_edges es).isSome
```

### Why It Was True
The definition of `drift_of_edge`:
```lean
def drift_of_edge (e : ExpandedEdge) : Option Real :=
  some (Real.log (3 + 1 / (e.src_residue : ℝ)) / Real.log 2 - (e.r_val : ℝ))
```

**Always returns `some`** — the computation is total. No `none` case ever appears.

Therefore, `mean_drift_of_edges` can never fail:
```lean
def mean_drift_of_edges (es : List ExpandedEdge) : Option Real :=
  let ws := es.map drift_of_edge  -- All elements are `some`
  if ws.any (· = none) then none  -- This is always false
  else
    some (...)                     -- Always takes this branch
```

### Lemma Proof Strategy

1. **Unfold definitions:** Expand `mean_drift_of_edges` and `drift_of_edge`
2. **Show all elements are `some`:** For any edge in the list, `drift_of_edge` produces `some`
3. **Prove negation:** Show `ws.any (· = none) = false`
4. **Simplify:** The `if` reduces to `some (...)`

**Proof (Lemma9_BasinCapture.lean):**
```lean
lemma mean_drift_defined_for_all (es : List ExpandedEdge) : (mean_drift_of_edges es).isSome := by
  unfold mean_drift_of_edges
  set ws := es.map drift_of_edge with h_ws
  -- ws consists entirely of some-values
  have h_all_some : ∀ w ∈ ws, w.isSome := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hw
    unfold drift_of_edge
    simp
  -- Therefore ws.any (· = none) = false
  have h_not_any : ¬(ws.any (· = none)) := by
    simp only [List.any_eq_true, List.mem_filter, not_exists]
    intro w hw
    have h_some := h_all_some w hw
    cases w with
    | some _ => simp at *
    | none => simp at h_some
  -- So mean_drift_of_edges returns some
  simp [h_not_any]
```

## Changes Made

### Lemma9_BasinCapture.lean
- **Removed:** `axiom mean_drift_defined_for_all`
- **Added:** `lemma mean_drift_defined_for_all` with constructive proof

## Axiom Count

**Before Phase 3:**
```
1. collatz_converges          (main theorem trust boundary)
2. mean_drift_defined_for_all (drift availability)  ← RETIRED
3. dp_global_descent          (DP reachability)
```

**After Phase 3:**
```
1. collatz_converges (src/CollatzAutomaton/MainTheorem.lean)
2. dp_global_descent (src/CollatzAutomaton/Lemma9_BasinCapture.lean)
```

**Progress:** 3 axioms → 2 axioms (1 retired this phase)

## Compilation Status

```
$ lake build
Build completed successfully.
```

✅ All files compile without errors.

## Impact on Codebase

**Before:**
```lean
have h := mean_drift_defined_for_all window_edges
simpa using h
```
This was an axiom assumption injected ad-hoc.

**After:**
```lean
have h := mean_drift_defined_for_all window_edges
simpa using h
```
Same call, but now `h` is a proven lemma with computational justification.

**Benefits:**
- ✅ One fewer axiom
- ✅ Cleaner trust boundary
- ✅ Proof is self-contained in Lemma 9 file
- ✅ Demonstrates structural property (totality of drift computation)

## Remaining Axioms

### 1. `dp_global_descent` (Lemma 9)
**Status:** Can be grounded in DpCertV2 once DP descent is formally integrated
**Difficulty:** Medium (requires path analysis + DP certificate import)

### 2. `collatz_converges` (MainTheorem)
**Status:** Ultimate goal — final convergence proof
**Difficulty:** High (depends on all lemmas + basin integration)

## Summary

**What was proven:** Every edge has a computable drift value → the mean drift of any edge list is always defined.

**Why it matters:** Removes the last "totality axiom" — drift computation is now verifiably total by construction.

**Next priority:** Ground `dp_global_descent` in the DP certificate (DpCertV2.lean) with proven min r-sum bounds.

---
**Status:** ✅ Phase 3 Complete — Drift Totality Axiom Retired
**Total Axioms Retired:** 3 (drift_weight_correct, log_sum_bound_from_dp, mean_drift_defined_for_all)
**Axioms Remaining:** 2 (dp_global_descent, collatz_converges)
