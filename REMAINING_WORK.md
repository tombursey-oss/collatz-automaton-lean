# Remaining Work: Two `sorry` Statements

## 1. `weighted_sum_negative` Proof (Line ~196)

**Current**:
```lean
theorem weighted_sum_negative (es : List ExpandedEdge)
    (h_len : es.length = 16)
    (h_r_sum : (es.map valuation_of_edge).foldl (· + ·) 0 ≥ 29) :
  match sum_of_edge_weights es with
  | some w => w ≤ 16 * log2_3 - 29
  | none   => True :=
  by
    unfold sum_of_edge_weights
    unfold mean_drift_of_edges
    sorry
```

**Type**: **Enumeration** (case analysis on 42 edges)

**Required Proof**:
Given a list of 16 edges from the 42 available in `edgeWeightsV0`, prove:
- `sum ≤ 16 * log₂(3) - 29`

**Proof Strategy**:
1. Each edge is looked up in `edgeWeightsV0` (42 finite entries)
2. By `edge_weight_encodes_drift`: `weight[i] = log₂(3 + 1/n[i]) - r[i]`
3. Sum: `∑ weights = ∑ log₂(3 + 1/n[i]) - ∑ r[i]`
4. Bound: `∑ log₂(3 + 1/n[i]) ≤ 16 * log₂(3)` (all n in automaton have log ≤ log₂(3))
5. Therefore: `sum ≤ 16 * log₂(3) - ∑ r[i] ≤ 16 * log₂(3) - 29` ✓

**Mechanization Difficulty**: **Medium**
- Automatable via code generation (similar to `MainTheorem` basin proofs)
- 42 finite cases, each requires 1 lookup + 1 arithmetic bound

**Estimate**: ~50 lines of generated Lean code

---

## 2. `h_mean_drift_bound` Proof (Line ~255)

**Current**:
```lean
have h_mean_drift_bound : d ≤ log2_3 - Real.ofNat 29 / 16 := by
  -- Derived from the weighted sum bound and division by 16
  -- h_weighted_sum gives us sum ≤ 16 * log₂(3) - 29
  -- Dividing both sides by 16: sum/16 ≤ log₂(3) - 29/16
  -- mean_drift = sum/16 by definition, so d ≤ log₂(3) - 29/16
  have h_w := h_weighted_sum
  unfold sum_of_edge_weights at h_w
  sorry
```

**Type**: **Algebraic** (field/arithmetic manipulation)

**Required Proof**:
Connect the sum bound to the mean bound:
- Given: `sum ≤ 16 * log₂(3) - 29`
- Goal: `mean ≤ log₂(3) - 29/16`

**Proof Strategy**:
1. `mean = sum / 16` (by definition of `mean_drift_of_edges`)
2. Divide both sides of the inequality by 16:
   `sum / 16 ≤ (16 * log₂(3) - 29) / 16`
3. Simplify RHS: `(16 * log₂(3) - 29) / 16 = log₂(3) - 29/16`
4. Therefore: `d ≤ log₂(3) - 29/16` ✓

**Mechanization Difficulty**: **Low**
- Pure field arithmetic
- Should be solvable with `field_simp` + `linarith`

**Estimate**: ~5-10 lines of Lean proof

---

## Quick Fix Attempt

### For `h_mean_drift_bound`:

```lean
have h_mean_drift_bound : d ≤ log2_3 - Real.ofNat 29 / 16 := by
  have h_w := h_weighted_sum
  unfold sum_of_edge_weights at h_w
  unfold mean_drift_of_edges at h_mean
  -- h_mean: mean_drift_of_edges es = some d
  -- h_w: sum of weights ≤ 16 * log2_3 - 29
  -- d = (sum of weights) / 16  [by definition of mean_drift_of_edges]
  -- Therefore: d ≤ (16 * log2_3 - 29) / 16 = log2_3 - 29/16
  have : d * 16 ≤ 16 * log2_3 - 29 := by
    -- This requires connecting h_w to the actual computation in mean_drift_of_edges
    sorry
  field_simp at this
  linarith
```

**Challenge**: The connection between `h_w` (sum bound) and `h_mean` (definition of d) requires unfolding `mean_drift_of_edges` and showing they compute the same sum.

---

## Proof Completion Roadmap

### Priority 1 (Immediate - ~30 min)
- [ ] Prove `h_mean_drift_bound` using field arithmetic
  - Start with `field_simp` + `ring`
  - Use `h_w` and definition of `mean_drift_of_edges`
  - Fallback: Keep as `sorry` but document clearly

### Priority 2 (Short-term - ~2 hours)
- [ ] Implement enumeration for `weighted_sum_negative`
  - Generate Lean code from the 42 edges
  - Similar to `MainTheorem` basin proof generation
  - Can automate with Python script

### Priority 3 (Optional - ~1 hour)
- [ ] Implement computational verification
  - Use `decide` on concrete window paths
  - Provides alternative, more explicit proof

---

## Summary Table

| Item | Type | Difficulty | Est. Time | Status |
|------|------|-----------|-----------|--------|
| `h_mean_drift_bound` | Algebra | Low | 30 min | ⏳ |
| `weighted_sum_negative` | Enumeration | Medium | 2 hrs | ⏳ |
| Overall mechanization | Hybrid | Medium | 2.5 hrs | ⏳ (60% done) |

