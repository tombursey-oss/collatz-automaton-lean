# Unified Proof Approach: Collatz Convergence via DP-Certified Descent
**Status:** Refined Implementation Roadmap (Audit-First)  
**Date:** January 2, 2026

---

## Executive Summary

This is the **refined, finalized** approach. It focuses on:
- **One core theorem** that proves the 64-window is uniform
- **Seven critical lemmas** in dependency order
- **Four failure points** to audit in existing code
- **Audit-first strategy** to validate before writing new code

---

## Part 1: The Core Claim (Everything Else Is Infrastructure)

### The One Theorem That Matters

All the DP work, all the finite-state encoding, all the DP certificates exist for *one purpose*:

**Establish this theorem:**
$$\forall n \text{ odd}, \quad \sum_{i=0}^{63} r\text{\_val}(n_i) \geq R_{\min}$$

where:
- $n_0 = n$ (starting odd integer)
- $n_{i+1} = T(n_i) = \frac{3n_i + 1}{2^{r\text{\_val}(n_i)}}$ (the odd-to-odd Collatz step)
- $r\text{\_val}(n) = \nu_2(3n + 1)$ (2-adic valuation)
- $R_{\min}$ is the minimum total weight over **all** length-64 paths in the DP graph

**In Lean:**
```lean
/-- The uniform 64-window bound: every odd integer's 64-step valuation sum ≥ R_min. -/
theorem window64_lower_bound :
  ∀ n : OddNat, (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ R_min
```

**Why this one theorem is everything:**
- If this holds for all odd n, then valuation sum is always ≥ R_min
- R_min > log₂(3) * 64 means 3^64 / 2^R_min < 1 (contraction)
- Contraction + affine expansion → n_64 < n (descent)
- Descent + basin = convergence ✓

**Everything else falls into three categories:**
1. **Infrastructure** — definitions and DP certificate
2. **Justifying the ∀n quantifier** — state coverage, edge semantics, path lifting
3. **Extracting descent** — contraction, recursion, strictness

---

## Part 2: The Seven Critical Lemmas (In Dependency Order)

### Lemma 1: Residue Coverage (Mapping Integers to States)

**Purpose:** Every odd integer belongs to exactly one graph state.

```lean
/-- Every odd natural number maps to a unique residue state. -/
def stateOf (n : OddNat) : State := n.val % (2^M)  -- or equivalent

/-- The mapping is total and well-defined. -/
lemma stateOf_total (n : OddNat) : ∃ s : State, stateOf n = s := ⟨stateOf n, rfl⟩

lemma stateOf_unique (n : OddNat) : ∃! s : State, stateOf n = s := sorry
```

**Critical check:**
- [ ] Is stateOf a function (deterministic)?
- [ ] Does every odd n map to some state?
- [ ] Is the mapping consistent with how states were defined in the DP solver?

**Failure mode:** If some odd n doesn't map to a state, the window bound might not apply to it.

---

### Lemma 2: Edge Extraction (Integer Step → Graph Edge)

**Purpose:** The actual Collatz step from any odd integer n follows an outgoing edge from stateOf(n), with the correct weight.

```lean
/-- The actual odd-step follows a unique graph edge with correct weight and target state. -/
lemma step_edge (n : OddNat) :
  ∃ e : Edge,
    e.from = stateOf n ∧
    e.to = stateOf (iterateOddStep n) ∧
    e.weight = r_val n
:= sorry

/-- Uniqueness: there is exactly one such edge (determinism of odd-step). -/
lemma step_edge_unique (n : OddNat) :
  ∃! e : Edge, 
    e.from = stateOf n ∧
    e.to = stateOf (iterateOddStep n) ∧
    e.weight = r_val n
:= sorry
```

**Critical check:**
- [ ] Does the proof actually show the edge exists in the DP graph (not just abstractly)?
- [ ] Does e.weight = r_val n, not some approximation?
- [ ] Does e.to match the actual residue of the next odd number?

**Failure mode:** If you only have "there exists an edge" or "for most edges," the ∀n quantifier breaks. The edge must be **the** edge, uniquely determined by n.

**This is the hinge:** Arithmetic ↔ Graph.

---

### Lemma 3: Path Lifting (Integer Trajectory → Graph Path)

**Purpose:** A 64-step integer trajectory lifts to a 64-vertex graph path, and the weight sum equals the valuation sum.

```lean
/-- Iterating 64 odd-steps from n gives a 64-vertex path in the graph. -/
def trajectory_to_path (n : OddNat) : PathLen 64 where
  start := stateOf n
  vertices := (List.range 64).map (fun i => stateOf (iterateOddStep i n))
  edges := (List.range 64).map (fun i => 
    (step_edge (iterateOddStep i n)).choose)  -- use Lemma 2 to extract the edge

/-- The weight sum of the path equals the valuation sum. -/
lemma path_weight_equals_valuation (n : OddNat) :
  (trajectory_to_path n).weight_sum =
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum
:= by
  -- Unfold trajectory_to_path
  -- Each edge weight = r_val of the step that produced it (by Lemma 2)
  -- Sum over 64 edges = sum of 64 valuations
  sorry
```

**Critical check:**
- [ ] Does this function exist and is it total?
- [ ] Is there a theorem that weight_sum = valuation_sum (not just "approximately equal")?
- [ ] Are the edges in the path actually those returned by step_edge (Lemma 2)?

**Failure mode:** If weight_sum ≠ valuation_sum, the DP bound doesn't transfer to integers. If trajectory_to_path only works for "most n," the ∀n quantifier breaks.

**This is the translation bridge:** Integer trajectory ↔ Graph path.

---

### Lemma 4: DP Global Bound (Certificate for All Length-64 Paths)

**Purpose:** The DP certificate guarantees that **every** length-64 path (from any starting vertex) has total weight ≥ R_min.

```lean
/-- The DP certificate lower-bounds every length-64 path. -/
lemma dp_global_descent (p : PathLen 64) :
  p.weight_sum ≥ R_min
:= sorry

/-- Equivalently: R_min is the minimum weight over all length-64 paths. -/
lemma min_weight_all_paths :
  R_min = (allPathsLen 64).map (fun p => p.weight_sum) |>.minimum
:= sorry
```

**Critical check:**
- [ ] Does dp_global_descent quantify over ALL paths, or only reachable ones?
- [ ] Is R_min defined as the global minimum, not a lower bound for a subset?
- [ ] If the DP uses domain restrictions, is there a lemma showing coverage (every vertex in domain)?

**Failure mode:** If the certificate only covers "reachable paths" or "most paths" or "paths from certain states," the ∀n quantifier breaks. The bound must apply universally.

**This is the DP oracle:** Guarantees that any 64-step path, no matter where it starts or what path it takes, has weight ≥ R_min.

---

### Lemma 5: Uniform Window Bound (The Core Theorem)

**Purpose:** Combine Lemmas 1–4 to get the one theorem that matters.

```lean
/-- The uniform 64-window bound: every odd integer has valuation sum ≥ R_min. -/
theorem window64_lower_bound (n : OddNat) :
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ R_min
:= by
  -- Proof:
  -- 1. By Lemma 3, the integer trajectory lifts to a graph path
  let p := trajectory_to_path n
  
  -- 2. By Lemma 3, the weight sum equals the valuation sum
  have h_weight : p.weight_sum = (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum :=
    path_weight_equals_valuation n
  
  -- 3. By Lemma 4, every path (including p) has weight ≥ R_min
  have h_bound : p.weight_sum ≥ R_min := dp_global_descent p
  
  -- 4. Combine
  rw [← h_weight]
  exact h_bound
```

**This is the theorem that makes "64 applies to all numbers" formally precise.**

It says: **For every odd n, the actual arithmetic trajectory, when lifted to the graph, follows a path guaranteed by the DP to have weight ≥ R_min. Thus, the valuation sum is always ≥ R_min.**

---

### Lemma 6: Window → Contraction (Affine Expansion)

**Purpose:** Use window64_lower_bound to get a multiplicative contraction.

Over 64 odd steps:
$$n_{64} = \frac{3^{64} n_0 + A}{2^S}, \quad S \geq R_{\min}$$

```lean
/-- After 64 odd-steps, the iterate is bounded by a contraction formula. -/
lemma oddIter64_contraction (n : OddNat) :
  let n_64 := iterateOddStep 64 n
  let S := (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum
  let A := accumulated_plus_ones n 64  -- explicit constant from affine formula
  (↑n_64 : ℚ) = (3^64 * ↑n + A) / 2^S ∧
  S ≥ R_min ∧
  (3 : ℚ)^64 / (2 : ℚ)^S ≤ (3 : ℚ)^64 / (2 : ℚ)^R_min
:= by
  -- Use window64_lower_bound to get S ≥ R_min
  have h_window := window64_lower_bound n
  -- Affine formula gives the equation
  sorry
```

**Critical check:**
- [ ] Is the affine formula correct?
- [ ] Does the proof use window64_lower_bound to establish S ≥ R_min?
- [ ] Is 3^64 / 2^R_min < 1 numerically verified?

**Failure mode:** If the ratio is ≤ 1 (not < 1), strict descent might not hold.

---

### Lemma 7: Strict Descent (Potential or Basin Argument)

**Purpose:** Convert the contraction into well-founded descent.

**Option A: Using a potential function Φ**

```lean
/-- Define potential for descent: Φ(n) = log(n) or similar. -/
def potential (n : ℕ) : ℝ := if n = 0 then 0 else Real.log (↑n)

/-- After 64 odd-steps with contraction, potential strictly decreases. -/
lemma oddIter64_strict_descent_via_potential (n : OddNat) (hn_large : n.val ≥ 64) :
  potential (iterateOddStep 64 n) < potential n.val
:= by
  have h_contract := oddIter64_contraction n
  have h_ratio : (3 : ℚ)^64 / (2 : ℚ)^R_min < 1 := contraction_margin_neg
  -- Combining: Φ(n_64) = log(n_64) ≤ log((ratio)*n + A)
  -- < log(ratio*n) + log(e) < log(n) [since ratio < 1]
  sorry
```

**Option B: Using basin + threshold**

```lean
def basin_threshold : ℝ := Real.log 64

/-- If Φ(n) below threshold, then n is in the verified basin. -/
lemma threshold_implies_basin (n : OddNat) :
  potential n.val < basin_threshold → n.val ≤ 63

/-- After 64 odd-steps from large n, potential drops toward threshold. -/
lemma oddIter64_toward_basin (n : OddNat) (hn_large : n.val ≥ 64) :
  potential (iterateOddStep 64 n) < potential n.val
:= sorry
```

**Critical check:**
- [ ] Is the measure (potential or direct) explicitly defined?
- [ ] Is descent strictly decreasing (< not ≤)?
- [ ] Does contraction_margin_neg establish the required numeric inequality?

**Failure mode:** If descent is only "≤" or if the additive constant is large enough to cancel the contraction, well-founded recursion fails.

---

## Part 3: The Four Real Failure Points

### Failure Point A: State-to-Integer Mapping

**Symptom:** You can claim "for all states s, there is a path," but stateOf is not a well-defined function or doesn't cover all odd integers.

**To audit:**
- [ ] Is stateOf(n) a function (not a relation)?
- [ ] Is it total (every odd n maps somewhere)?
- [ ] Is it consistent with the DP solver's state definition?

**If this breaks:** The ∀n quantifier is not universal.

---

### Failure Point B: Edge Semantics

**Symptom:** The edges in the graph don't correspond to actual Collatz steps.

**To audit:**
- [ ] Does step_edge prove that every odd integer's Collatz step follows an outgoing edge?
- [ ] Does the edge weight equal r_val(n), not an approximation or average?
- [ ] Does the edge target equal stateOf(T(n))?
- [ ] Is the edge unique (step_edge_unique)?

**If this breaks:** The graph doesn't model arithmetic.

---

### Failure Point C: DP Certificate Scope

**Symptom:** The DP certificate only guarantees R_min for "reachable" paths or a subset of starts, not all paths.

**To audit:**
- [ ] Does dp_global_descent quantify over ALL paths (allPathsLen 64)?
- [ ] Is R_min the global minimum (min over all vertices)?
- [ ] If the DP uses domain restrictions, is coverage proven (every state reachable)?

**If this breaks:** R_min doesn't bound all real trajectories.

---

### Failure Point D: Strictness of Descent

**Symptom:** The contraction is ≤ 1 (not < 1), or the additive term is large enough that descent doesn't work.

**To audit:**
- [ ] Is contraction_margin_neg proven (3^64 / 2^R_min < 1)?
- [ ] Is it numerically verified (Lean #eval)?
- [ ] Does the potential/basin argument handle the additive constant?

**If this breaks:** Descent might not terminate.

---

## Part 4: Audit-First Checklist for Existing Code

**Before writing new lemmas, verify that existing code provides:**

### Critical Path Validation

1. **Lemma 3: trajectory_to_path or path_lifting**
   - [ ] Function exists that maps odd integer → 64-vertex path?
   - [ ] Theorem: path.weight_sum = valuation sum? (exact equality)
   - If YES → Lemma 3 is done; if NO → Priority 1

2. **Lemma 4: dp_global_descent or equivalent**
   - [ ] Lemma claiming: every length-64 path has weight ≥ R_min?
   - [ ] Quantifies over ALL paths (not reachable subset)?
   - If YES → Lemma 4 is done; if NO → Priority 2

3. **Lemmas 1–2: stateOf + step_edge**
   - [ ] Mapping from odd integers to states?
   - [ ] Proof that Collatz step follows a graph edge?
   - If YES → Lemmas 1–2 are done; if NO → Priority 3

4. **Lemma 5: window64_lower_bound**
   - [ ] Does it already exist?
   - If NO, and 1–4 exist → Can be derived mechanically (low priority)

5. **Lemma 6: oddIter64_contraction**
   - [ ] Affine formula lemma?
   - [ ] Connects to window64_lower_bound?
   - If NO → Priority 4

6. **Lemma 7: Strict descent**
   - [ ] Potential function or basin threshold defined?
   - [ ] Proof that oddIter64 gives strict descent?
   - If NO → Priority 5

### Expected Status (Revised)

- **Likely exists:** Lemmas 1, 2 (partially; edge semantics might be incomplete)
- **Needs audit:** Lemmas 3, 4 (the critical path bridges)
- **Definitely missing:** Lemmas 5, 6, 7

---

## Part 5: Implementation Order (Audit-First)

If **both Lemmas 3 and 4 are correct**, then:
- Lemma 5 (window64_lower_bound) is purely mechanical
- Lemmas 6–7 are straightforward algebra

If **either Lemma 3 or 4 is weak/incorrect**, the whole proof fails.

### Recommended Sequence

1. **Audit** Lemmas 3 and 4 in existing code
   - Verify trajectory_to_path and weight_sum semantics
   - Verify dp_global_descent quantifies over all paths
   
2. **Fix** Lemmas 3 and 4 if needed (high priority)

3. **Implement** Lemmas 1–2 (usually straightforward residue system)

4. **Derive** Lemma 5 (mechanical once 1–4 are solid)

5. **Prove** Lemma 6 (affine formula, uses Lemma 5)

6. **Prove** Lemma 7 (strict descent, uses Lemma 6)

7. **Assemble** main convergence theorem (uses basins + descent)

---

## Part 6: The Minimal Correctness Proof

Once the seven lemmas exist and are correct, here's the minimal proof that "64 applies to all numbers":

```lean
theorem uniform_window_bound :
  ∀ n : OddNat, (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ R_min :=
  window64_lower_bound  -- Lemma 5

theorem uniform_contraction :
  ∀ n : OddNat, n.val ≥ 64 → (iterateOddStep 64 n) < n.val :=
  fun n hn => by
    have h5 := window64_lower_bound n
    have h6 := oddIter64_contraction n
    have h7 := oddIter64_strict_descent_via_potential n hn
    omega  -- or linarith, depending on formulation
```

That's it. The universality of the 64-window is now formally proven.

---

## Part 7: What Could Still Go Wrong (4 Specific Failure Points)

1. **Auditing Lemma 3:** If trajectory_to_path doesn't exist or weight_sum ≠ valuation_sum, stop. Build it.
2. **Auditing Lemma 4:** If dp_global_descent doesn't quantify over all paths, stop. Fix the certificate statement.
3. **Edge semantics (Lemma 2):** If the proof doesn't show the actual step follows an actual edge, it's insufficient. Require full edge_match proof.
4. **Contraction strictness (Lemma 7):** If the descent is only "≤", the recursion doesn't work. Must have "<".

---

## Part 8: Summary

| # | Lemma | Status | Priority | Proof Difficulty |
|---|-------|--------|----------|------------------|
| 1 | Residue Coverage | Likely exists | 3 | Low |
| 2 | Edge Extraction | Partially exists | 3 | Medium |
| 3 | Path Lifting | **CRITICAL** | 1 | High |
| 4 | DP Global Bound | **CRITICAL** | 2 | High |
| 5 | Window Bound | Derivable | 4 | Low |
| 6 | Contraction | Missing | 5 | Medium |
| 7 | Strict Descent | Missing | 6 | Medium |

**The real bottleneck:** Lemmas 3 and 4. If these are correct, the rest is mechanical.

**The real risk:** One of them being stated too weakly (e.g., "there exists a path" instead of "the actual path").

---

## Final Checklist Before Declaring Proof Complete

- [ ] **Lemma 3:** trajectory_to_path exists and path.weight_sum = valuation_sum is proven
- [ ] **Lemma 4:** dp_global_descent quantifies over ALL paths of length 64
- [ ] **Lemma 1:** stateOf is total and deterministic
- [ ] **Lemma 2:** step_edge proves the actual Collatz step follows a graph edge
- [ ] **Lemma 5:** window64_lower_bound is derived from 1–4
- [ ] **Lemma 6:** oddIter64_contraction uses window64_lower_bound and affine formula
- [ ] **Lemma 7:** oddIter64_strict_descent uses contraction and contraction_margin_neg
- [ ] **contraction_margin_neg:** 3^64 / 2^R_min < 1 is verified
- [ ] **basin_rows_reach_1_data:** All odd n ≤ 63 verified
- [ ] **collatz_converges:** Main theorem assembled using basin + descent + recursion
- [ ] **Build:** `lake build` completes with 0 errors

---

**Status:** This document is the final specification. Use it as the gold standard for what must be proven.

