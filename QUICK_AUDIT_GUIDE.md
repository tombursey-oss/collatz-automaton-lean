# Quick Audit Guide: Validating the Seven Critical Lemmas
**Status:** Rapid Assessment Tool  
**Date:** January 2, 2026

---

## How to Use This Guide

1. **For each lemma below**, check the "Verification Questions"
2. **If all boxes ☑ check**, mark status as ✅ **VALID**
3. **If any box ❌ fails**, mark as ❌ **NEEDS WORK** and note the issue
4. **Read the "Red Flags"** section — if any apply, the lemma is insufficient even if boxes check

---

## Lemma 1: Residue Coverage

**File to check:** `Core.lean`, `MainTheorem.lean`, or new `ResidueSystem.lean`

**What to look for:**
```lean
def stateOf (n : OddNat) : State := ...
```

### Verification Questions

- ☐ **Is stateOf defined as a function** (not a relation)?  
  - BAD: `relation stateOf : OddNat → State → Prop`
  - GOOD: `def stateOf (n : OddNat) : State := n.val % (2^M)`

- ☐ **Every odd integer maps to some state** (totality)?
  - Look for: `lemma stateOf_total : ∀ n : OddNat, ∃ s : State, stateOf n = s`
  - Or implicit in definition (if modulo operation always produces a state)

- ☐ **Is stateOf deterministic** (same input → same output)?
  - Should be obvious from definition; if non-deterministic, it fails

- ☐ **Does stateOf align with DP graph vertices**?
  - Check: Are the states in the DP graph exactly `{0, 1, ..., 2^M - 1}` or equivalent?
  - Check: Is the M value consistent?

### Red Flags

❌ **INSUFFICIENT if:**
- stateOf only covers "most" odd integers (not all)
- stateOf is non-deterministic or relation-based
- States in definition ≠ states in DP certificate
- No documentation of what M is or why it's sufficient

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

---

## Lemma 2: Edge Extraction

**File to check:** `MainTheorem.lean`, `Lemma9_BasinCapture.lean`, or new `EdgeSemantics.lean`

**What to look for:**
```lean
lemma step_edge (n : OddNat) : ∃ e : Edge, ...
lemma step_edge_unique (n : OddNat) : ∃! e : Edge, ...
```

### Verification Questions

- ☐ **Does a lemma claim that every odd n's step follows an edge**?
  - Look for: `step_edge`, `step_edge`, or `edge_of_n`
  - Must quantify over ALL odd n, not just reachable ones

- ☐ **Does the edge have the correct FROM state**?
  - `e.from = stateOf n` ✓
  - Or `e.from = residue_of n` (if residue_of matches stateOf) ✓

- ☐ **Does the edge have the correct TO state**?
  - `e.to = stateOf (iterateOddStep n)` ✓
  - NOT `e.to = next_state (stateOf n)` (unless proven equivalent)

- ☐ **Does the edge weight match the actual valuation**?
  - `e.weight = r_val n` ✓
  - NOT `e.weight ≈ r_val n` or `e.weight ≥ r_val n`

- ☐ **Is uniqueness proven** (step_edge_unique)?
  - Confirms that the Collatz step is deterministic

### Red Flags

❌ **INSUFFICIENT if:**
- The lemma only applies to "reachable" or "typical" odd integers
- The proof assumes the edge exists rather than proving it exists in the DP graph
- The edge weight is an approximation or bound, not exact equality
- The target state is not stateOf(next integer)
- The proof doesn't actually reference the DP certificate

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

---

## Lemma 3: Path Lifting (CRITICAL)

**File to check:** `Lemma9_BasinCapture.lean`, `MainTheorem.lean`, or new `PathLifting.lean`

**What to look for:**
```lean
def trajectory_to_path (n : OddNat) : PathLen 64 := ...
lemma path_weight_equals_valuation (n : OddNat) : 
  (trajectory_to_path n).weight_sum = ∑ r_val(...) := ...
```

### Verification Questions

- ☐ **Does a function map integer → 64-vertex path exist**?
  - `trajectory_to_path` or similar name
  - Takes an odd integer, returns a path of length 64
  - Returns a real graph path (edges that exist in the graph)

- ☐ **Does the path consist of actual graph edges**?
  - Each edge should come from the edge set (not abstract)
  - Each edge should satisfy the step_edge property (Lemma 2)

- ☐ **Is there a theorem that path.weight_sum = valuation_sum**?
  - **Exact equality**, not ≥ or ≤
  - Look for: `path_weight_equals_valuation` or `weight_sum_matches_valuation`
  - Formula should be: `∑_{i=0}^{63} weight(edge_i) = ∑_{i=0}^{63} r_val(n_i)`

- ☐ **Is the proof correct**?
  - The key steps should be:
    1. Each edge comes from step_edge (Lemma 2)
    2. Each edge's weight = r_val from step_edge
    3. Sum all 64 edges' weights = sum of 64 r_vals

### Red Flags

❌ **INSUFFICIENT if:**
- trajectory_to_path doesn't exist
- weight_sum ≠ valuation_sum (only ≥ or ≤)
- The path is "abstract" or doesn't consist of real edges
- The proof doesn't use Lemma 2 to establish the edge weights
- The function only works for "most" or "reachable" starting points

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

**Why this is critical:** Without this, the DP certificate (which bounds path weights) cannot bound real valuations.

---

## Lemma 4: DP Global Bound (CRITICAL)

**File to check:** `Lemma9_BasinCapture.lean`, `DpCertV2.lean`, or new `DPCertificate.lean`

**What to look for:**
```lean
lemma dp_global_descent (p : PathLen 64) : p.weight_sum ≥ R_min := ...
```

### Verification Questions

- ☐ **Does a lemma claim all length-64 paths have weight ≥ R_min**?
  - Must quantify over ALL paths, not a subset
  - Look at the type signature: `∀ p : PathLen 64, p.weight_sum ≥ R_min`

- ☐ **Is R_min defined as a global minimum**?
  - `R_min := (allPathsLen 64).map weight_sum |>.minimum`
  - NOT `R_min := minimum weight over reachable paths`
  - NOT `R_min := some constant chosen a priori`

- ☐ **Does the proof actually use the DP certificate**?
  - Should invoke some DP computation or certificate data
  - Should not be a magic constant
  - Should be traceable to DPSummaryV2 or DpCertV2

- ☐ **Is the coverage complete**?
  - Does every possible 64-vertex path in the graph have weight ≥ R_min?
  - If the DP used domain restrictions, is there a lemma proving every state is in the domain?

### Red Flags

❌ **INSUFFICIENT if:**
- The lemma only applies to "reachable paths from B₀" or similar subset
- R_min is defined as lower bound for a subset, not global minimum
- The proof doesn't actually reference a certificate or computation
- The DP solver output is trusted without a correctness proof
- "Every path" is not quantified universally in the statement

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

**Why this is critical:** Without this, the DP bound doesn't constrain all trajectories.

---

## Lemma 5: Window Bound (Derivable)

**File to check:** `MainTheorem.lean` or new `WindowBound.lean`

**What to look for:**
```lean
theorem window64_lower_bound (n : OddNat) :
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ R_min := ...
```

### Verification Questions

- ☐ **Is the theorem stated correctly**?
  - Quantifies over all OddNat
  - RHS is exactly `≥ R_min` (not ≥ something else)
  - LHS sums exactly 64 r_val terms

- ☐ **Is it derived from Lemmas 1–4**?
  - Proof should use trajectory_to_path (Lemma 3)
  - Proof should use path_weight_equals_valuation (Lemma 3)
  - Proof should use dp_global_descent (Lemma 4)
  - Proof structure: `valuation_sum = path.weight_sum ≥ R_min`

- ☐ **Is the proof short and mechanical**?
  - If the proof is long or has sorry/sorry, check Lemmas 3–4 again

### Red Flags

❌ **INSUFFICIENT if:**
- Lemmas 3 or 4 are marked as insufficient
- The proof has sorry or admit
- The theorem is stated as ≥ some other constant (not R_min)

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

---

## Lemma 6: Contraction

**File to check:** `Lemma9_BasinCapture.lean` or new `Contraction.lean`

**What to look for:**
```lean
lemma oddIter64_contraction (n : OddNat) :
  let n_64 := iterateOddStep 64 n
  let S := ∑ r_val(...)  -- valuation sum
  (↑n_64 : ℚ) ≤ (3^64 / 2^S) * ↑n + C ∧
  S ≥ R_min := ...
```

### Verification Questions

- ☐ **Is there an affine formula lemma**?
  - Claim: `n_64 = (3^64 * n + A) / 2^S` for explicit A
  - Or equivalently: `n_64 ≤ (3^64 / 2^S) * n + C`

- ☐ **Does the proof use window64_lower_bound**?
  - To establish `S ≥ R_min`

- ☐ **Are the constants (A, C) computable**?
  - Should be able to compute explicit bounds for the additive term

- ☐ **Is 3^64 / 2^R_min < 1 verified numerically**?
  - Look for a lemma `contraction_margin_neg` or #eval check

### Red Flags

❌ **INSUFFICIENT if:**
- No affine formula lemma exists
- The proof doesn't use window64_lower_bound
- Constants are left as sorry
- The contraction ratio is ≤ 1 (not < 1)

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

---

## Lemma 7: Strict Descent

**File to check:** `MainTheorem.lean`, `Lemma9_BasinCapture.lean`, or new `Descent.lean`

**What to look for:**
```lean
lemma oddIter64_strict_descent (n : OddNat) (hn : n.val ≥ 64) :
  iterateOddStep 64 n < n := ...
```

### Verification Questions

- ☐ **Is the measure defined** (potential or direct nat argument)?
  - Either `def potential (n : ℕ) : ℝ := Real.log ↑n`
  - Or use direct `iterateOddStep 64 n < n`

- ☐ **Is descent strictly decreasing** (< not ≤)?
  - Proof should show `n_64 < n`, not `n_64 ≤ n`

- ☐ **Does the proof use oddIter64_contraction**?
  - To get the formula and ratio bound

- ☐ **Does the proof verify contraction_margin_neg**?
  - To establish that 3^64 / 2^R_min < 1
  - This makes the inequality strict

### Red Flags

❌ **INSUFFICIENT if:**
- Only proves `n_64 ≤ n` (not strict)
- The proof doesn't use the contraction formula
- contraction_margin_neg is missing
- The additive constant is large enough to cancel the contraction

### Status
- [ ] ✅ VALID
- [ ] ❌ NEEDS WORK (note: __________________)

---

## Summary: Quick Status Check

Fill in the table below:

| Lemma | File | Status | Issue |
|-------|------|--------|-------|
| 1. Residue Coverage | | ✅/❌ | |
| 2. Edge Extraction | | ✅/❌ | |
| 3. Path Lifting | | ✅/❌ | |
| 4. DP Global Bound | | ✅/❌ | |
| 5. Window Bound | | ✅/❌ | |
| 6. Contraction | | ✅/❌ | |
| 7. Strict Descent | | ✅/❌ | |

**If Lemmas 3 and 4 are ✅:** The proof is essentially complete; remaining work is mechanical.

**If Lemma 3 or 4 is ❌:** Stop and fix that lemma. It's the critical bottleneck.

---

## Next Steps Based on Audit Results

**All ✅:** Proceed to implement Lemmas 5–7 (mechanical)

**Lemmas 3–4 ❌, others ✅:** Priority 1: fix Lemmas 3–4

**Lemmas 1–2 ❌, others ✅:** Priority 2: implement Lemmas 1–2 (straightforward)

**Lemmas 5–7 ❌, others ✅:** Priority 3: derive/prove Lemmas 5–7

**Mixed:** Use this guide to triage issues and prioritize fixes

---

**Use this guide to identify exactly which lemmas are missing or weak, then refer back to UNIFIED_PROOF_APPROACH_REFINED.md for detailed specifications.**

