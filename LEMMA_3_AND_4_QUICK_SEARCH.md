# Quick Reference: Lemma 3 vs. Lemma 4 (Side-by-Side Search)
**Status:** Visual Quick Reference  
**Date:** January 2, 2026

---

## THE TWO CRITICAL PATTERNS

### LEMMA 3: Equality Pattern

```
SEARCHING FOR:
────────────────────────────────────────────────────────────

lemma [name] ... :
  [something].weight_sum = (List.range 64).map (fun i => r_val ...) |>.sum := ...

MARKS OF VALIDITY:
  ✅ Uses     = (equality, not ≥ or ≤)
  ✅ Sums     r_val for each step
  ✅ Exactly  64 terms
  ✅ Pattern  weight_sum = ∑ r_val(...)

MARKS OF INVALIDITY:
  ❌ Uses     ≥ or ≤ (inequality)
  ❌ Sums     something other than r_val
  ❌ Fewer    than 64 terms
  ❌ Pattern  weight_sum ≥ something (wrong direction)
```

**In your code, look for:**
- File: Lemma9_BasinCapture.lean (most likely)
- Lemma names: path_weight_*, weight_sum_*, lift_path_*, trajectory_*
- Key substring: `weight_sum = ` followed eventually by ` |>.sum`

---

### LEMMA 4: Universal Quantification Pattern

```
SEARCHING FOR:
────────────────────────────────────────────────────────────

lemma [name] (p : PathLen 64) :
  p.weight_sum ≥ R_min := ...

OR

lemma [name] :
  ∀ p : PathLen 64, p.weight_sum ≥ R_min := ...

MARKS OF VALIDITY:
  ✅ Quantifies over ALL paths    (∀ p : PathLen 64)
  ✅ Compares weight_sum ≥ R_min  (R_min is the global lower bound)
  ✅ No domain restriction        (not "∀ reachable p" or "∀ p from v")
  ✅ Pattern ∀ p, weight_sum ≥ R_min

MARKS OF INVALIDITY:
  ❌ Quantifies ∃ (existence, not universality)
  ❌ Compares weight_sum ≤ R_min  (inequality reversed)
  ❌ Restricts to subset          ("reachable," "from," "in," etc.)
  ❌ Pattern ∀ v, min(paths from v) ≥  (about vertices, not paths)
```

**In your code, look for:**
- File: Lemma9_BasinCapture.lean or DpCertV2.lean
- Lemma names: dp_global_*, every_path_*, min_weight_all_*
- Key substring: `weight_sum ≥ R_min` with `∀ p : PathLen`

---

## SIDE-BY-SIDE EXAMPLES

### ✅ GOOD Lemma 3 Examples

```lean
-- Example 1: Explicit equality
lemma path_weight_equals_valuation (n : OddNat) :
  (trajectory_to_path n).weight_sum = 
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum := by
  sorry

-- Example 2: Different name, same pattern
lemma weight_sum_matches_trajectory (n : OddNat) :
  let p := trajectory_to_path n
  p.weight_sum = (trajectory_valuations n 64).sum := by
  sorry

-- Example 3: Embedded in larger proof
lemma oddIter64_contraction (n : OddNat) :
  let S := (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum
  let w := (trajectory_to_path n).weight_sum
  w = S ∧ S ≥ R_min := by
  constructor
  · sorry  -- THIS IS LEMMA 3
  · sorry
```

### ❌ BAD Lemma 3 Examples

```lean
-- Example 1: Inequality instead of equality
lemma path_weight_bounds_valuation (n : OddNat) :
  (trajectory_to_path n).weight_sum ≥ (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum := by
  sorry
  -- ❌ WRONG: Uses ≥ instead of =

-- Example 2: Wrong direction
lemma valuation_bounds_path (n : OddNat) :
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ (trajectory_to_path n).weight_sum := by
  sorry
  -- ❌ WRONG: Backwards inequality

-- Example 3: Only for "reachable" paths
lemma reachable_path_weight (n : OddNat) (h_reach : n ∈ reachableSet) :
  (trajectory_to_path n).weight_sum = ∑ r_val(...) := by
  sorry
  -- ⚠️  RESTRICTIVE: Only for subset of starting points
```

---

### ✅ GOOD Lemma 4 Examples

```lean
-- Example 1: Explicit quantification
lemma dp_global_descent (p : PathLen 64) :
  p.weight_sum ≥ R_min := by
  sorry

-- Example 2: Explicit ∀ syntax
lemma every_path_has_min_weight :
  ∀ p : PathLen 64, p.weight_sum ≥ R_min := by
  intro p
  sorry

-- Example 3: Equivalence to minimum
lemma min_weight_all_paths :
  R_min = (allPathsLen 64).map weight_sum |>.minimum ∧
  ∀ p : PathLen 64, p.weight_sum ≥ R_min := by
  constructor
  · sorry
  · intro p
    sorry
```

### ❌ BAD Lemma 4 Examples

```lean
-- Example 1: Existence instead of universality
lemma some_path_has_min_weight :
  ∃ p : PathLen 64, p.weight_sum ≥ R_min := by
  sorry
  -- ❌ WRONG: ∃ instead of ∀

-- Example 2: Reversed inequality
lemma dp_global_upper_bound (p : PathLen 64) :
  p.weight_sum ≤ R_max := by
  sorry
  -- ❌ WRONG: Looking for ≥ R_min, not ≤ R_max

-- Example 3: Only for reachable paths
lemma reachable_path_bound (p : PathLen 64) (h : p.start ∈ reachableSet) :
  p.weight_sum ≥ R_min := by
  sorry
  -- ❌ WRONG: Only for subset (h_reach constraint)

-- Example 4: About vertices, not paths
lemma vertex_min_weight (v : Vertex) :
  (minPathWeightFrom v 64) ≥ R_min := by
  sorry
  -- ❌ WRONG: About vertices/paths from vertices, not all paths
```

---

## GREP PATTERNS FOR QUICK FIND

### For Lemma 3
```bash
# Grep pattern: Find "weight_sum = ... |>.sum"
grep -r "weight_sum\s*=" src/ | grep "\.sum\|r_val"

# Grep pattern: Find trajectory_to_path and its theorems
grep -r "trajectory_to_path" src/ -A 5 | grep "weight_sum"

# Grep pattern: Find path lifting lemmas
grep -r "lift_path\|path_lift\|path_weight" src/
```

### For Lemma 4
```bash
# Grep pattern: Find "weight_sum ≥ R_min"
grep -r "weight_sum.*≥\|≥.*R_min" src/

# Grep pattern: Find universal path bounds
grep -r "∀.*PathLen\|forall.*Path" src/ | grep "weight_sum"

# Grep pattern: Find dp_global or similar
grep -r "dp_global\|global_descent\|global_bound" src/
```

---

## THE MINIMAL TEST

Run these commands in the `c:\collatz_automaton` directory:

### Test 1: Does Lemma 3 exist with equality?
```powershell
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "weight_sum\s*=" | 
  Select-String "r_val|valuation"
```

**Expected output:** A line showing `weight_sum = ... |>.sum` or similar

### Test 2: Does Lemma 4 exist with universal quantification?
```powershell
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "weight_sum.*≥.*R_min|R_min.*weight_sum" | 
  Select-String "∀|PathLen" | 
  Select-String -NotMatch "∃"
```

**Expected output:** A line showing `∀ p : PathLen 64, weight_sum ≥ R_min` or equivalent

---

## DECISION TREE

```
Q1: Did you find Lemma 3 with "weight_sum ="?
├─ YES → Q2: Is the RHS exactly "∑ r_val(...)"?
│  ├─ YES → ✅ LEMMA 3 FOUND (go to Lemma 4)
│  └─ NO  → Check file manually, verify formula
└─ NO  → Not in codebase (needs implementation)

Q2: Did you find Lemma 4 with "∀ p : PathLen 64, weight_sum ≥ R_min"?
├─ YES → Q3: Does it mention the DP certificate?
│  ├─ YES → ✅ LEMMA 4 FOUND (both critical lemmas present!)
│  └─ NO  → Check proof justification in file
└─ NO  → Not in codebase (needs implementation)

RESULT:
├─ Both ✅ → Proof is essentially complete, implement Lemmas 5–7
├─ Only L3 ✅ → Implement Lemma 4 (critical)
├─ Only L4 ✅ → Implement Lemma 3 (critical)
└─ Neither ✅ → Implement both (critical path)
```

---

## WHAT TO DO WHEN YOU FIND THEM

1. **Copy the exact lemma signature** into a new file for reference
2. **Check the proof:** Is it `sorry` or actually proven?
3. **Verify the types:** Do the types match exactly?
4. **Check consistency:** Do all lemmas use the same definitions?
   - Same `r_val`?
   - Same `R_min`?
   - Same `iterateOddStep`?

---

## FINAL CHECK

Once you find both lemmas, answer:

**For Lemma 3:**
- [ ] Found and has form: `weight_sum = ∑ r_val(...)`?
- [ ] Sums exactly 64 terms?
- [ ] Uses actual r_val (2-adic valuation)?

**For Lemma 4:**
- [ ] Found and has form: `∀ p : PathLen 64, weight_sum ≥ R_min`?
- [ ] Quantifies over ALL 64-paths (not a subset)?
- [ ] R_min is the global minimum?

If all boxes checked → **Both critical lemmas are present and likely correct.**

If any box unchecked → **Need to investigate further or implement.**

