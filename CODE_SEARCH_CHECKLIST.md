# Code Search Checklist: Finding the Critical Lemmas in Existing Code
**Status:** Search Guide  
**Date:** January 2, 2026

---

## How to Use This Guide

For each lemma below:
1. **Search in Lean files** for the lemma name (or similar names)
2. **Check the signature** against the "Expected Signature" below
3. **Mark whether found** and record the file location
4. **If signature is different**, note the discrepancy

---

## CRITICAL: Lemma 3 — Path Lifting

### Expected Signatures

One or more of:
```lean
def trajectory_to_path (n : OddNat) : PathLen 64 := ...
def path_of_integer (n : OddNat) : Path := ...
def integer_to_graph_path (n : OddNat) : List Edge := ...
```

```lean
lemma path_weight_equals_valuation (n : OddNat) :
  (trajectory_to_path n).weight_sum = ∑ r_val(...) := ...

lemma weight_sum_matches_valuation (n : OddNat) :
  (path_of_integer n).weights.sum = (valuations n).sum := ...
```

### Search Strategy

```powershell
# Search for function definitions
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "def (trajectory|path|integer_to)" | Select-String -Pattern "OddNat.*Path|OddNat.*Edge"

# Search for valuation/weight theorems
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "weight_sum|valuation" | Select-String -Pattern "equals|matches|Eq"
```

### What Makes It Valid

✅ **VALID if:**
- The function maps OddNat → PathLen 64 or similar
- There's a theorem showing weight_sum = valuation_sum (exact equality)
- The path consists of actual graph edges (not abstract)
- The proof uses edge extraction (Lemma 2) to connect steps to edges

❌ **INSUFFICIENT if:**
- Only shows weight_sum ≥ valuation_sum or weight_sum ≤ valuation_sum
- Only applies to "reachable" starting points
- The function is named but not proven to be correct
- No theorem linking weights to valuations

### Status
- **File:** ___________________
- **Found:** Yes / No
- **Signature matches:** Yes / No / Partial
- **Notes:** _______________________

---

## CRITICAL: Lemma 4 — DP Global Bound

### Expected Signatures

One or more of:
```lean
lemma dp_global_descent (p : PathLen 64) :
  p.weight_sum ≥ R_min := ...

lemma min_weight_all_paths :
  R_min = (allPathsLen 64).map weight_sum |>.minimum := ...

lemma every_path_min_weight (p : Path) (h_len : p.length = 64) :
  p.weight_sum ≥ R_min := ...
```

### Search Strategy

```powershell
# Search for R_min definition
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "R_min|Rmin"

# Search for path weight bounds
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "weight_sum.*R_min|R_min.*weight"

# Search for global descent
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "dp_global|global_descent|global_bound"
```

### What Makes It Valid

✅ **VALID if:**
- R_min is defined as a global constant (or lemma establishes it)
- dp_global_descent quantifies over ALL paths of length 64
- The statement is `∀ p : PathLen 64, p.weight_sum ≥ R_min`
- There's a lemma proving R_min = minimum over all paths (or certificate guarantees it)

❌ **INSUFFICIENT if:**
- Only applies to "reachable paths" or "paths from certain vertices"
- R_min is a lower bound for a subset of paths
- The lemma is stated as existence ("∃ path with weight ≥") not universality ("∀ path")
- No explanation of how the certificate guarantees the bound

### Status
- **File:** ___________________
- **Found:** Yes / No
- **Signature matches:** Yes / No / Partial
- **Notes:** _______________________

---

## Lemma 1 — Residue Coverage

### Expected Signatures

```lean
def stateOf (n : OddNat) : State := ...
def state_of_integer (n : OddNat) : State := ...
def residue_of (n : OddNat) : ℕ := ...

lemma stateOf_unique (n : OddNat) : ∃! s : State, stateOf n = s := ...
```

### Search Strategy

```powershell
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "def (stateOf|residue|state_of)" | Select-String "OddNat"
```

### What Makes It Valid

✅ **VALID if:**
- stateOf is a function from OddNat to State
- Every odd n maps to some state
- The mapping is deterministic

### Status
- **File:** ___________________
- **Found:** Yes / No

---

## Lemma 2 — Edge Extraction

### Expected Signatures

```lean
lemma step_edge (n : OddNat) :
  ∃ e : Edge, e.from = stateOf n ∧
              e.to = stateOf (iterateOddStep n) ∧
              e.weight = r_val n := ...

lemma edge_of_step (n : OddNat) :
  ∃! e : Edge, (edge_matches n e) := ...

lemma step_follows_edge (n : OddNat) :
  ∃ e : Edge, (the_edge_from n) = e ∧ 
              (e in dpGraph.edges) := ...
```

### Search Strategy

```powershell
Get-ChildItem src -Include "*.lean" -Recurse | Select-String -Pattern "step_edge|edge_of|follows_edge" | Select-String "OddNat"
```

### What Makes It Valid

✅ **VALID if:**
- Proves every odd step follows an outgoing edge
- Edge has correct from/to/weight properties
- Edge is from the DP graph (not abstract)

### Status
- **File:** ___________________
- **Found:** Yes / No

---

## Lemma 5 — Window Bound (Derivable)

### Expected Signatures

```lean
theorem window64_lower_bound (n : OddNat) :
  (List.range 64).map (fun i => r_val (iterateOddStep i n)) |>.sum ≥ R_min := ...

theorem uniform_valuation_bound (n : OddNat) :
  ∑_{i=0}^{63} r_val(n_i) ≥ R_min := ...
```

### Search Strategy

```powershell
Get-ChildItem src -Include "*.lean" -Recurse | Select-String "window64|uniform_valuation" | Select-String "R_min"
```

### What Makes It Valid

✅ **VALID if:**
- Exists and is proven
- Can derive from Lemmas 1–4 if not already present

### Status
- **File:** ___________________
- **Found:** Yes / No

---

## Lemma 6 — Contraction

### Expected Signatures

```lean
lemma oddIter64_contraction (n : OddNat) :
  let n_64 := iterateOddStep 64 n
  let S := ∑ r_val(...)
  (↑n_64 : ℚ) ≤ (3^64 / 2^S) * ↑n + C ∧ S ≥ R_min := ...

lemma affine_formula (n : OddNat) (L : ℕ) :
  (iterateOddStep L n : ℚ) = (3^L * n + A) / 2^(∑ r_vals) := ...
```

### Search Strategy

```powershell
Get-ChildItem src -Include "*.lean" -Recurse | Select-String "contraction|affine" | Select-String "64|iterate"
```

### What Makes It Valid

✅ **VALID if:**
- Connects affine formula to valuation bound
- Uses window64_lower_bound to establish S ≥ R_min

### Status
- **File:** ___________________
- **Found:** Yes / No

---

## Lemma 7 — Strict Descent

### Expected Signatures

```lean
lemma oddIter64_strict_descent (n : OddNat) (hn : n.val ≥ 64) :
  iterateOddStep 64 n < n := ...

lemma contraction_margin_neg :
  (3 : ℚ)^64 / (2 : ℚ)^R_min < 1 := ...

lemma descent_via_potential (n : OddNat) (hn : n.val ≥ 64) :
  potential (iterateOddStep 64 n) < potential n.val := ...
```

### Search Strategy

```powershell
Get-ChildItem src -Include "*.lean" -Recurse | Select-String "strict_descent|contraction_margin|descent"
```

### What Makes It Valid

✅ **VALID if:**
- Proves n_64 < n (strict, not just ≤)
- Uses contraction_margin_neg (3^64 / 2^R_min < 1)

### Status
- **File:** ___________________
- **Found:** Yes / No

---

## Summary Table

| Lemma | Expected File | Status | Found? | Signature Match? |
|-------|--------|--------|--------|------------------|
| 1. Residue Coverage | Core.lean | | Yes/No | Yes/No/Partial |
| 2. Edge Extraction | MainTheorem.lean | | Yes/No | Yes/No/Partial |
| 3. Path Lifting | Lemma9.lean | **CRITICAL** | Yes/No | Yes/No/Partial |
| 4. DP Global Bound | Lemma9.lean | **CRITICAL** | Yes/No | Yes/No/Partial |
| 5. Window Bound | MainTheorem.lean | Derivable | Yes/No | Yes/No/Partial |
| 6. Contraction | Lemma9.lean | Missing | Yes/No | Yes/No/Partial |
| 7. Strict Descent | MainTheorem.lean | Missing | Yes/No | Yes/No/Partial |

---

## Next Steps

1. **Fill out this form** by searching for each lemma
2. **For Lemmas 3 and 4:** If missing or wrong signature, stop and implement those
3. **For Lemmas 1–2:** Implement if missing (straightforward)
4. **For Lemmas 5–7:** Derive/prove from the others (mechanical once 1–4 are solid)

---

**Use this checklist to rapidly identify what's already in the codebase vs. what needs to be built.**

