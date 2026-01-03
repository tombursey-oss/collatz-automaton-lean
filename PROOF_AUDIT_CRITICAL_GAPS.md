# PROOF AUDIT: CRITICAL GAPS ANALYSIS

**Date:** January 2, 2026  
**Status:** ⚠️ CRITICAL ISSUES IDENTIFIED  
**Confidence in Current Proof:** LOW (gaps must be closed before completion)

---

## Executive Summary

The user's comprehensive audit (10-step proof strategy) identifies **5 critical checkpoints (A–E)** that must be kernel-verified for the proof to be valid. Against these checkpoints, the current codebase has **significant gaps**:

| Checkpoint | Requirement | Current Status | Risk |
|-----------|-------------|-----------------|------|
| **(A) Graph Semantics** | Edges carry true valuation weights (ν₂) | ❌ MISSING | **CRITICAL** |
| **(B) Path Lifting** | Arithmetic trajectories lift to graph paths with exact weight match | ⚠️ PARTIAL | **CRITICAL** |
| **(C) DP Coverage** | Universal lower bound on all reachable paths proven | ⚠️ HAS SORRY | **CRITICAL** |
| **(D) Strict Descent** | T^L(n) contracts using A_L control | ❌ NOT FORMALIZED | **CRITICAL** |
| **(E) Basin Capture** | Finite verification + descent entry proven | ⚠️ PARTIAL | **HIGH** |

**Key Finding:** The proof currently rests on unvalidated assumptions; without closing these gaps, the claim "all n reach 1" is not kernel-verified.

---

## Deep-Dive Analysis by Checkpoint

### ❌ Checkpoint A: Graph Semantics — Edge Weights = True Valuations

**What's Required:**
- Finite state graph where each edge has a weight equal to ν₂(3n+1) for the actual integer step
- No placeholder weights (like `residue % 10`)
- Weights must be defined for **all transitions**, not conditionally

**Current Code Status (Graph.lean, Lemma8_DensityFloor.lean):**

**Line 20–22 in Graph.lean:**
```lean
def transitionRel (s t : State) : Prop :=
  ∃ e ∈ expandedEdgesV2,
    s.residue = e.src_residue ∧ s.branch = (e.src_b = 1) ∧
    t.residue = e.dst_residue ∧ t.branch = (e.dst_b = 1)
```
**Issue:** No weight field. The edge record comes from `ExpandedEdge` (from CSV import). Nowhere in the visible code are edge weights extracted or validated.

**Line 89–99 in Lemma8_DensityFloor.lean (window_of_path):**
```lean
def window_of_path (p : PathLen L) : Window := by
  have h_vals : (List.range L).map (fun i => 
    if h : i < p.steps.length then (p.steps.get ⟨i, h⟩).residue % 10 else 0
  ).length = L := by simp [List.length_range]
  exact {
    vals := (List.range L).map (fun i => 
      if h : i < p.steps.length then (p.steps.get ⟨i, h⟩).residue % 10 else 0
    )
    len_eq := h_vals
  }
```
**Issue:** The window extraction uses **`residue % 10`**, which is NOT the 2-adic valuation. This is a **fatal error**:
- ν₂(3n+1) ∈ [1, ∞)
- `residue % 10` ∈ [0, 9]
- These are completely different functions
- **The proof cannot be correct with this definition.**

**Verdict:** ❌ BLOCKED. Cannot proceed until:
1. Edge weights in `transitionRel` include the true ν₂ valuation
2. `window_of_path` extracts actual valuations, not `residue % 10`
3. Validation that edge weights match arithmetic steps

**Time to Fix:** ~2–3 hours (requires rethinking edge representation and validation)

---

### ⚠️ Checkpoint B: Path Lifting — Exact Weight Correspondence

**What's Required:**
- For every odd integer n, the first L arithmetic odd-block steps produce a length-L path in the graph
- Sum of edge weights in that path = sum of arithmetic valuations (S_L)
- This must be **proven**, not assumed

**Current Code Status (Lemma8_DensityFloor.lean, lines 101–120):**

```lean
/-- Extract valuations from a length-L path... -/
lemma window_of_path_valid (p : PathLen L) :
  (window_of_path p).vals.length = L := by
  exact (window_of_path p).len_eq

lemma reachable_path_yields_reachable_window (p : PathLen L) (h : reachable p.start) :
  ReachableWindow (window_of_path p) := by
  exact ⟨p, h, rfl⟩
```

**Issues:**
1. These lemmas are **trivial structural facts**, not the hard part
2. The **critical claim is missing**: given an arithmetic trajectory (odd n, apply T L times), that sequence of n values corresponds to a valid graph path
3. No lemma proves: `(arithmetic_valuation_sum n L) = (graph_path_weight_sum n L)`
4. Because `window_of_path` uses `residue % 10`, any such lemma would be **false anyway**

**Verdict:** ⚠️ INCOMPLETE. The lemmas exist but are too weak. Needs:
1. Fix `window_of_path` to use real valuations (blocks Checkpoint A fix)
2. Prove that arithmetic trajectories lift to valid graph paths
3. Prove weight equality (S_L = graph sum)

**Time to Fix:** ~1–2 hours (after Checkpoint A is fixed)

---

### ⚠️ Checkpoint C: DP Coverage — Universal Reachability Bound

**What's Required:**
- DP solver computed minimum total weight over all length-16 paths in reachable subgraph
- Formally proven: ∀ reachable path, weight_sum ≥ 29
- No `sorry`, no conditional scope, universal quantifier over **all odd integers** (not just enumerated states)

**Current Code Status (Lemma8_DensityFloor.lean, lines 207–233):**

```lean
theorem dp_coverage :
  ∀ w, ReachableWindow w → ∃ (w' : Window) (hw' : w' ∈ dp_all_windows), 
    dominates w w' :=
by
  intro w hw
  obtain ⟨p, hp_reachable, hp_window⟩ := hw
  use dpWindow0
  refine ⟨by simp [dp_all_windows], ?_⟩
  unfold dominates
  have h_min_sum : valuation_sum w ≥ 29 := by
    -- This is the crux: the DP certificate guarantees...
    sorry  -- DP certificate validation (see note below)
  calc
    valuation_sum w ≥ 29 := h_min_sum
    _ = valuation_sum dpWindow0 := (dp_window0_sum_eq_29).symm
```

**Critical Issues:**

1. **Explicit `sorry`** at the hardest step: proving that every reachable window has sum ≥ 29
   - This is the entire DP guarantee; without it, the claim is unvalidated

2. **Scope is conditional:** The statement says "if w is a ReachableWindow, then it dominates dpWindow0"
   - But does every odd integer n give a ReachableWindow?
   - If `reachable p.start` only covers 42 enumerated states, then this doesn't apply to all odd n
   - **The universal claim "∀ odd n, S_16(n) ≥ 29" is NOT proven**

3. **DP certificate never validated in Lean:**
   - The `dpMinWindowsV2` data is imported but treated as an oracle
   - The claim "minimum path sum = 29" is stated in comments but not kernel-checked

**Verdict:** ⚠️ BLOCKED. The sorry must be filled. Options:
1. Enumerate all reachable paths and verify each (feasible for 42 states × 16 steps)
2. Construct explicit DP proof structure in Lean
3. Write proof validation code that produces a Lean certificate

Additionally: Must prove that **all odd integers** arise from reachable states, not just 42 enumerated nodes.

**Time to Fix:** ~3–4 hours (DP validation is the hardest part of the whole proof)

---

### ❌ Checkpoint D: Strict Descent — Contraction Formula

**What's Required:**
- Prove the affine expansion: T^L(n) = (3^L · n + A_L) / 2^{S_L}
- Show that A_L is controlled tightly enough
- Prove: for S_L ≥ 29 and large enough n, we have T^L(n) < n (strict descent)
- Must handle the constant term A_L carefully to ensure < not just ≤

**Current Code Status:**

**Lemma 1.3 (Affine Formula) in Lemma Hierarchy:** Status = ⚠️ PARTIAL  
No kernel proof found in codebase.

**Lemma 5.1 (Contraction Inequality):** Status = ❌ NOT STARTED  
Not present.

**Lemma 5.3 (Strict Descent):** Status = ❌ NOT STARTED  
Not present.

**Related:** MainTheorem.lean has:
```lean
lemma dp_global_descent : ∃ k, iterate_k k n ≤ 63 ∧ n > 63 → ...
```
This is **basin capture**, not strict descent. These are different:
- Strict descent: ∀ n > threshold, T^L(n) < n (or similar measure decrease)
- Basin capture: ∀ n > threshold, ∃ k, T^L^k(n) < basin_threshold

**Verdict:** ❌ COMPLETELY MISSING. Requires:
1. Formalize affine expansion (Lemma 1.3)
2. Prove contraction from valuation floor (Lemma 5.1)
3. Prove strict descent via well-founded recursion (Lemma 5.3)

This is the **hardest missing piece**. The arithmetic is sound, but Lean formalization is non-trivial.

**Time to Fix:** ~2–3 hours (Lemma 1.3 is the bottleneck)

---

### ⚠️ Checkpoint E: Basin Capture — Finite Verification + Descent Entry

**What's Required:**
- Prove that all odd n ≤ 63 (+ even reductions) reach 1
- Prove that all odd n > threshold eventually drop ≤ 63 via descent
- Combine into: ∀ n ≠ 0, ∃ k, iterate_k(k, n) = 1

**Current Code Status (from earlier sessions):**

BasinVerificationV2.lean exists with:
```lean
structure BasinRow := 
  (n : Nat) (path_to_1 : List Nat) ...

def basin_rows_reach_1_data : List BasinRow := [...]
```

**Issues:**
1. Signature has been mismatched with how it's used
2. Integration with descent (Checkpoint D) is not present
3. No strong induction that combines even reduction + odd descent + basin

**Verdict:** ⚠️ PARTIAL. Exists but:
1. Needs integration with strict descent (blocks on Checkpoint D)
2. Needs strong induction tying everything together (Lemma 6.3)

---

## Missing Lemmas (from Lemma Hierarchy)

The following lemmas are marked ⚠️ PARTIAL or ❌ NOT STARTED in the hierarchy and block completion:

| Lemma | Status | Blocks | Time |
|-------|--------|--------|------|
| **1.3 (Affine Formula)** | ⚠️ Partial | 5.1, 5.3, 6.3 | 2–3 hrs |
| **2.1 (State Encoding)** | ⚠️ Partial | Path lifting | 1 hr |
| **2.2 (Edge Extraction)** | ⚠️ Partial | Path lifting | 1 hr |
| **5.1 (Contraction)** | ❌ Missing | 5.3, 6.3 | 1–2 hrs |
| **5.3 (Strict Descent)** | ❌ Missing | 6.3 | 1 hr |
| **6.2 (Basin Capture)** | ⚠️ Partial | 6.3 | 1–2 hrs |
| **6.3 (Main Theorem)** | ❌ Missing | FINISH | 30 min |

---

## The Critical Path to Fix

Based on dependencies:

```
Fix Graph Semantics (A)
  ↓
Fix Path Lifting (B)
  ↓
Fill DP Coverage Sorry (C)
  ↓
Implement Affine Formula (1.3)
  ↓
Implement Contraction (5.1)
  ↓
Implement Strict Descent (5.3)
  ↓
Complete Basin Capture (6.2)
  ↓
Assemble Main Theorem (6.3) ← PROOF COMPLETE
```

**Estimated Total Time:** 11–14 hours

**Bottlenecks:**
1. Checkpoint A (graph weights): 2–3 hours
2. Checkpoint C (DP validation): 3–4 hours
3. Checkpoint D (affine + descent): 2–3 hours

---

## Immediate Action Items

### Priority 1: Verify Current Graph Semantics (1 hour)
- [ ] Locate definition of `ExpandedEdge` in `ExpandedEdgesV2.lean`
- [ ] Confirm whether it includes a `weight` or `valuation` field
- [ ] If yes: verify it equals ν₂(3n+1) in arithmetic
- [ ] If no: MUST add this field before any further work

### Priority 2: Fix window_of_path (30 min – 1 hour)
- [ ] Replace `residue % 10` with **actual valuation extraction**
- [ ] Either:
  - Store ν₂ in the State/Edge record, OR
  - Compute ν₂(3n+1) from consecutive states in path
- [ ] Prove that the extracted valuations match arithmetic

### Priority 3: Fill DP Coverage Sorry (2–3 hours)
- [ ] Validate the DP certificate data in Lean
- [ ] Either enumerate proof or write validator
- [ ] Remove sorry and prove universally

### Priority 4: Implement Lemma 1.3 (Affine Formula) (2–3 hours)
- [ ] State the expansion: T^L(n) = (3^L·n + A_L) / 2^{S_L}
- [ ] Prove by induction on L
- [ ] Establish tight bound on A_L

### Priority 5: Implement Lemmas 5.1, 5.3, 6.3 (4–5 hours)
- [ ] Use affine formula + valuation floor to prove contraction
- [ ] Establish well-founded measure
- [ ] Assemble final theorem

---

## Truth-Table: What's Proven vs. Claimed

| Statement | Proof Status | Issues |
|-----------|--------------|--------|
| ν₂ is well-defined | ✅ Proven | None |
| If n odd, then 3n+1 is even | ✅ Proven | None |
| T(n) = (3n+1)/2^{ν₂(3n+1)} is odd | ✅ Proven | None |
| Affine expansion T^L(n) = (3^L·n + A_L)/2^{S_L} | ⚠️ Claimed in comments | **NOT kernel-proven** |
| Graph is a finite automaton on states | ✅ Defined | But edges lack weights (Checkpoint A) |
| Arithmetic trajectories lift to graph paths | ⚠️ Claimed, lemmas exist | **But window_of_path uses residue % 10** (fatal) |
| Every reachable path has sum ≥ 29 | ⚠️ Claimed with sorry | **DP validation missing** |
| Therefore all odd n have S_16(n) ≥ 29 | ❌ NOT proven | Depends on above |
| 3^16 < 2^29 therefore contraction | ⚠️ True arithmetically | **Lemma 5.1 not formalized** |
| Therefore ∃ threshold above which strict descent | ❌ NOT proven | **Lemma 5.3 missing** |
| All odd n ≤ 63 reach 1 | ✅ Likely proven | Must verify integration |
| All n ≠ 0 reach 1 | ❌ NOT proven | Depends on assembling 6.3 |

---

## Conclusion

The current proof is **not ready**. The architecture is sound and the plan is solid, but critical gaps remain:

1. **Graph semantics are incomplete** (no edge weights, placeholder valuations)
2. **DP coverage has an unfilled sorry** (the hardest step)
3. **Strict descent is not formalized** (missing Lemmas 1.3, 5.1, 5.3)
4. **Main theorem assembly is incomplete** (Lemma 6.3)

**To declare proof complete, all checkpoints A–E must have kernel proofs (no sorry/admit).**

---

## Recommended Next Session

**Focus:** Fix Checkpoints A and C first, as they are preconditions for everything else.

1. **Checkpoint A** (1–2 hours): Add weights to graph, fix window_of_path
2. **Checkpoint C** (3–4 hours): Validate DP certificate, fill sorry
3. **Checkpoint D** (2–3 hours): Implement Lemmas 1.3, 5.1, 5.3
4. **Checkpoint E** (1–2 hours): Verify basin, implement 6.3

Total: ~8–12 hours to fully kernel-verified proof.
