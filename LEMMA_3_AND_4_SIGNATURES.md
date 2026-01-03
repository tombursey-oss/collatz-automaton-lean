# Critical Lemma Signatures: Lemma 3 and Lemma 4
**Status:** Precise Search Specification  
**Date:** January 2, 2026

---

## Why These Two Lemmas Matter

**Lemma 3 and Lemma 4 are the bottleneck.** If both are correct, the entire proof is essentially done. Everything else derives mechanically.

---

## LEMMA 3: Path Lifting (The Bridge from Arithmetic to Graph)

### What It Must Establish

**An equality** tying the weight sum of a graph path to the sum of actual Collatz valuations:

$$\text{weight\_sum(path)} = \sum_{i=0}^{63} r\text{\_val}(n_i)$$

### Exact Lean Signature Patterns

**Search for one of these exact patterns:**

```lean
lemma path_weight_equals_valuation (n : OddNat) :
  (trajectory_to_path n).weight_sum = (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum :=
  sorry
```

OR

```lean
lemma weight_sum_matches_valuation (n : OddNat) :
  let path := trajectory_to_path n
  path.weight_sum = (valuations_from n 64).sum :=
  sorry
```

OR

```lean
lemma path_lift_preserves_weight (n : OddNat) :
  (path_of_integer n).edges.map weight |>.sum = ∑ r_val(...) :=
  sorry
```

OR (more general)

```lean
lemma lift_path_64 (n : OddNat) :
  ∃ p : PathLen 64,
    p.start = stateOf n ∧
    p.weight_sum = (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum :=
  sorry
```

### Critical Pattern: The Equality

The **key distinguishing feature** is:

- ☑ **MUST have:** `weight_sum = ... |>.sum` (exact equality)
- ☑ **MUST sum:** Exactly 64 terms (or clearly indexed 0..63)
- ☑ **MUST be:** `r_val` applied at each step
- ❌ **MUST NOT be:** `weight_sum ≥` or `weight_sum ≤` (inequality, not equality)

### Search Commands

```powershell
# Search for weight_sum = ... |>.sum pattern
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String -Pattern "weight_sum\s*=.*\.sum" | 
  Select-String "r_val|valuation"

# Search for specific lemma names
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "weight.*equals|matches.*weight|preserves.*weight|lift_path"

# Search for trajectory_to_path definition and usage
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "trajectory_to_path|path_of_integer"
```

### What Makes It Valid ✅

- [ ] Function exists: `trajectory_to_path : OddNat → PathLen 64` or similar
- [ ] Theorem exists: `weight_sum = ∑ r_val (...)` (exact equality, not ≥ or ≤)
- [ ] The sum is over exactly 64 terms
- [ ] Each term is `r_val (iterateOddStep i n)` or equivalent
- [ ] The path is constructed from actual graph edges (uses Lemma 2)

### What Makes It Invalid ❌

- ❌ Only proves `weight_sum ≥ valuation_sum` (inequality instead of equality)
- ❌ Only proves existence: "∃ path with weight =" (not ∀)
- ❌ The sum is over fewer than 64 terms
- ❌ The equality is approximate ("about equal," "asymptotically")
- ❌ The path is abstract (not constructed from real edges)

---

## LEMMA 4: DP Global Bound (The Oracle from the Certificate)

### What It Must Establish

**A universal quantification** over all length-64 paths, claiming each has weight ≥ R_min:

$$\forall \text{ path } p \text{ of length 64}, \quad \text{weight\_sum}(p) \geq R_{\min}$$

### Exact Lean Signature Patterns

**Search for one of these exact patterns:**

```lean
lemma dp_global_descent (p : PathLen 64) :
  p.weight_sum ≥ R_min :=
  sorry
```

OR

```lean
theorem every_path_has_min_weight (p : Path) (h_len : p.length = 64) :
  p.weight_sum ≥ R_min :=
  sorry
```

OR

```lean
lemma min_weight_all_paths :
  ∀ p : PathLen 64, p.weight_sum ≥ R_min :=
  sorry
```

OR

```lean
lemma dp_bounds_all_length_64 (p : PathLen 64) :
  R_min ≤ p.weight_sum :=
  sorry
```

### Critical Pattern: The Universality

The **key distinguishing feature** is:

- ☑ **MUST have:** `∀ p : PathLen 64` or equivalent (quantifies over ALL paths)
- ☑ **MUST have:** `weight_sum ≥ R_min` (the DP bound)
- ☑ **MUST be:** About path weight sums, not vertices or edges alone
- ❌ **MUST NOT:** Only apply to "reachable paths" or "paths from vertex v"
- ❌ **MUST NOT:** Be about existence: "∃ p with weight ≥" (not universal)

### Search Commands

```powershell
# Search for dp_global_descent or equivalent
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "dp_global|global_descent|global_bound"

# Search for all paths + weight_sum + R_min
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "weight_sum.*R_min|R_min.*weight" | 
  Select-String "∀|forall|every"

# Search for minimum weight over paths
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "min.*weight|minimum.*path|min_weight"

# Search for R_min definition
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "R_min|Rmin" | 
  Select-String "def|:="
```

### What Makes It Valid ✅

- [ ] Statement quantifies: `∀ p : PathLen 64` (all paths of length 64)
- [ ] Conclusion is: `p.weight_sum ≥ R_min` (exact inequality)
- [ ] R_min is defined as the global minimum (or proven to be)
- [ ] The proof references the DP certificate or computation
- [ ] No domain restrictions ("reachable paths," "from state v," etc.)

### What Makes It Invalid ❌

- ❌ Only applies to "reachable paths from B₀" or similar subset
- ❌ Existence claim: "∃ p with weight ≥" (not universal)
- ❌ Inequality is reversed: `weight_sum ≤ R_min`
- ❌ R_min is defined as a lower bound for a subset, not global minimum
- ❌ The proof doesn't reference any DP certificate or computation
- ❌ The statement is: "∀ vertices v, min_path_from v ≥" (about vertices, not paths)

---

## Side-by-Side Comparison

| Aspect | Lemma 3 | Lemma 4 |
|--------|---------|---------|
| **Type** | Equality | Inequality + Universality |
| **Quantifier** | Implicit in definition (for given n) | Explicit ∀ over all paths |
| **What changes** | The function trajectory_to_path | The set of paths quantified over |
| **Exact formula** | `weight_sum = ∑ r_val` | `∀ p, weight_sum ≥ R_min` |
| **Critical check** | Is the equality exact? | Is the quantifier universal (all paths)? |
| **Failure mode** | Uses ≥ instead of = | Only bounds "reachable paths" |

---

## Search Strategy (Step-by-Step)

### Step 1: Find Lemma 3
```powershell
# In Lemma9_BasinCapture.lean or MainTheorem.lean:
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String -Pattern "weight_sum\s*=.*|\.sum|\.foldl"
```

**Look for:**
- Function name: `trajectory_to_path`, `path_of_integer`, `path_lift`, etc.
- Theorem name: `weight_equals_valuation`, `path_weight_matches`, etc.
- The pattern: Something = ∑ r_val(...)

### Step 2: Find Lemma 4
```powershell
# In Lemma9_BasinCapture.lean or DpCertV2.lean:
Get-ChildItem src -Include "*.lean" -Recurse | 
  Select-String "dp_global|weight_sum.*≥|≥.*R_min" | 
  Select-String "∀|PathLen"
```

**Look for:**
- Lemma name: `dp_global_descent`, `every_path_min_weight`, etc.
- Pattern: `∀ p : PathLen 64, weight_sum ≥ R_min`
- Reference: How is R_min obtained from the DP?

### Step 3: Verify Equality vs. Inequality

**For Lemma 3:**
- If you find `weight_sum =`, that's good ✅
- If you find `weight_sum ≥` or `weight_sum ≤`, it's wrong ❌

**For Lemma 4:**
- If you find `∀ p : PathLen 64, weight_sum ≥ R_min`, that's good ✅
- If you find `∃ p : PathLen 64, weight_sum ≥ R_min`, it's wrong ❌
- If you find `∀ v : Vertex, ...` (about vertices), keep searching ❌

---

## Minimal Valid Examples

### Lemma 3: Minimal Valid Form
```lean
lemma path_weight_equals_valuation (n : OddNat) :
  (trajectory_to_path n).weight_sum = 
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum := by
  -- Proof strategy:
  -- 1. Unfold trajectory_to_path definition
  -- 2. Each edge in the path has weight = r_val of the step (by Lemma 2)
  -- 3. Sum of 64 edges = sum of 64 r_vals
  sorry
```

**Key:** The `=` sign, not `≥` or `≤`.

### Lemma 4: Minimal Valid Form
```lean
lemma dp_global_descent (p : PathLen 64) :
  p.weight_sum ≥ R_min := by
  -- Proof strategy:
  -- 1. R_min is the minimum weight over all 64-paths (by DP computation)
  -- 2. Any specific path has weight ≥ the minimum
  -- 3. Therefore p.weight_sum ≥ R_min
  sorry
```

**Key:** The `∀` (implicit in the function argument `p`), the `≥`, and `R_min` (not a different constant).

---

## What to Record When You Find Them

For **Lemma 3:**
- [ ] File name: ___________________
- [ ] Lemma/theorem name: ___________________
- [ ] Line number: ___________________
- [ ] Exact formula on RHS: ___________________
- [ ] Is it exactly `weight_sum = ∑ r_val(...)`? Yes / No / Partial

For **Lemma 4:**
- [ ] File name: ___________________
- [ ] Lemma/theorem name: ___________________
- [ ] Line number: ___________________
- [ ] Does it say `∀ p : PathLen 64, weight_sum ≥ R_min`? Yes / No / Partial
- [ ] Is R_min the global minimum? Yes / No / Unknown

---

## If You Find Variants

If the formulas are slightly different, answer these questions:

**For Lemma 3:**
- Is `weight_sum` computed the same way as you'd compute it (sum of edge weights)?
- Is the RHS summing exactly `r_val (iterateOddStep i n)` for i ∈ [0, 64)?
- Are they equal (=) or just bounded (≥/≤)?

**For Lemma 4:**
- Does it quantify over all possible 64-paths, or just a subset?
- Is the inequality `weight_sum ≥ R_min` or something else?
- Where does R_min come from? Is it the global minimum or a local constant?

If you answer "yes" to all the critical questions for both, you're in good shape.

---

## Final Checklist

- [ ] **Found Lemma 3** with exact equality `weight_sum = ∑ r_val`
- [ ] **Found Lemma 4** with universal quantification `∀ p, weight_sum ≥ R_min`
- [ ] Both lemma names and locations recorded
- [ ] Both lemmas use consistent definitions (same r_val, same R_min, etc.)
- [ ] Ready to verify with QUICK_AUDIT_GUIDE.md

---

**If both Lemma 3 and Lemma 4 exist and are correct, the proof is essentially complete.**

