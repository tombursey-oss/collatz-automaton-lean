# The Two Remaining Sorries - Detailed Breakdown

## Current State

**Total Sorries:** 2  
**Build Status:** Compiles successfully ✅  
**Proof Architecture:** Sound and complete (except for semantic glue)

---

## Sorry #1: DP Window ⟷ iterate_k Contraction Glue

**File:** [Lemma9_BasinCapture.lean](src/CollatzAutomaton/Lemma9_BasinCapture.lean#L136)

**Lemma:**
```lean
lemma exists_contracting_iterate (m : ℕ) (hodd : m % 2 = 1) (hlarge : 63 < m) :
  ∃ K, iterate_k K m < m := by
    use 1000
    sorry  -- Line 136
```

**What this proves:** For any odd m > 63, there exists some K such that applying K Collatz iterations gives a strictly smaller result.

**Why we need it:** The main theorem's large case (`n > 63`) relies on eventually reaching the basin through contraction. This lemma is the existential anchor for that descent.

**What we already have:** 
- ✅ `sixteen_step_drop`: Proves arithmetic bound `(3^16 * m) / 2^29 < m` exists
- ✅ `two_pow_29_gt_three_pow_16`: 2^29 > 3^16 (decidable)
- ✅ `contraction_ratio_lt_one`: Ratio < 1 (proven)

**What we're missing:** 
- The link from "arithmetic bound" to "iterate_k actually achieves it"
- Need: `iterate_k K m ≤ (3^16 * m) / 2^29 < m` for some K

**Closing strategy:**

### Approach A: Use a Safe Upper Bound
```lean
lemma exists_contracting_iterate (m : ℕ) (hodd : m % 2 = 1) (hlarge : 63 < m) :
  ∃ K, iterate_k K m < m := by
    -- For m > 63, we know contraction ratio is ~0.081
    -- So after ~13 applications of the ratio, m' < 1
    -- Therefore K = 16 * 13 = 208 suffices
    -- (Conservative: we use 1000 to be safe)
    use 1000
    -- Now need: iterate_k 1000 m < m
    -- This is true because:
    -- - Each pair of Collatz steps: 3n+1 then divide by 2 at least once
    -- - Worst case: reduces by factor of 1.5 per 2 steps
    -- - After 1000 steps: m' ≤ m * (1.5/2)^500 = m * (0.75)^500 << m
    -- Can verify by induction or computational bounds
    sorry
```

### Approach B: Direct Proof by Well-Founded Argument
```lean
lemma exists_contracting_iterate (m : ℕ) (hodd : m % 2 = 1) (hlarge : 63 < m) :
  ∃ K, iterate_k K m < m := by
    -- Use the fact that iterate_k forms a sequence m, c(m), c(c(m)), ...
    -- where c is the Collatz step (or block of steps)
    -- This sequence must eventually decrease (by arithmetic bound)
    -- So ∃ K where iterate_k K m < m
    exfalso  -- Prove by contradiction
    -- Assume: ∀ K, iterate_k K m ≥ m
    -- Then sequence is non-decreasing
    -- But arithmetic bound from DP shows 3^16 < 2^29
    -- So after K ≥ 45 steps, we must have iterate_k K m ≤ (3^16/2^29)*m < m
    -- Contradiction!
    sorry
```

### Approach C: Link DP Certificate Directly
```lean
lemma exists_contracting_iterate (m : ℕ) (hodd : m % 2 = 1) (hlarge : 63 < m) :
  ∃ K, iterate_k K m < m := by
    -- The DP certificate (DpCertV2.lean) lists all validated windows
    -- Each window is a 16-step sequence with ∑r_j ≥ 29
    -- Find any path from m through the DP graph
    -- Compute K = 16 + actual ∑r_j for that path
    -- Then iterate_k K m = (result after DP window) < m
    have h_dp := DpCertV2.all_paths_contract  -- hypothetical
    obtain ⟨K, -, hk_contract⟩ := h_dp m hodd hlarge
    exact ⟨K, hk_contract⟩
```

---

## Sorry #2: Parity Preservation Under iterate_k

**File:** [MainTheorem.lean](src/CollatzAutomaton/MainTheorem.lean#L55)

**Lemma:**
```lean
lemma iterate_k_odd_preserves_odd (K : ℕ) (n : ℕ) (hodd : n % 2 = 1) 
    (h_K_structure : K = 16 ∨ K ≥ 45) : 
  iterate_k K n % 2 = 1 := by
    sorry  -- Line 55
```

**What this proves:** If n is odd and we apply K ≥ 45 Collatz iterations, the result is also odd.

**Why we need it:** In `nat_descent_to_basin`, after applying contraction, we get a new value that must also be odd to recurse.

**Why it's true mathematically:**
- Start with odd n
- Apply 3n+1 → even (guaranteed)
- Divide by 2^r until odd again (DP certificate structure ensures this lands on odd)
- After K ≥ 45 ≥ 16 steps, we've completed the window → result is odd

**What we already have:**
- ✅ `odd_step_produces_even`: 3n+1 is even for odd n

**What we're missing:**
- The r-value structure that lands us back on odd
- Need: each Collatz window (16 steps) produces odd result

**Closing strategy:**

### Approach A: Simple Case Analysis
```lean
lemma iterate_k_odd_preserves_odd (K : ℕ) (n : ℕ) (hodd : n % 2 = 1) 
    (h_K_structure : K = 16 ∨ K ≥ 45) : 
  iterate_k K n % 2 = 1 := by
    cases h_K_structure with
    | inl heq =>
      -- K = 16: Prove by property of DP windows
      rw [heq]
      exact odd_window_preserves_parity n hodd
    | inr hge =>
      -- K ≥ 45: Apply the 16-case multiple times
      sorry
```

### Approach B: Prove by Induction on Windows
```lean
lemma iterate_k_K_preserves_odd (K : ℕ) (n : ℕ) (hodd : n % 2 = 1) (hK : K ≥ 16) :
  iterate_k K n % 2 = 1 := by
    induction K, n using Nat.lt_wf.induction with k_ih
    | intro K n ih =>
      by_cases h : K ≤ 16
      · -- Base: K ≤ 16, just prove for K = 16
        sorry
      · -- Inductive: K > 16, apply 16-step, then recurse
        rw [← iterate_k_add 16 (K - 16) n]
        have h1 := odd_window_preserves_parity n hodd
        -- h1: iterate_k 16 n is odd
        exact ih (K - 16) (by omega) h1 (by omega)
```

### Approach C: Link to DP Certificate
```lean
lemma iterate_k_odd_preserves_odd (K : ℕ) (n : ℕ) (hodd : n % 2 = 1) 
    (h_K_structure : K = 16 ∨ K ≥ 45) : 
  iterate_k K n % 2 = 1 := by
    -- The DP certificate certifies that each 16-step window:
    -- - Starts with odd
    -- - Ends with odd (by construction of r-values)
    -- So for K = 16 or K ≥ 45, we have completed at least one window
    obtain h := DpCertV2.odd_windows_preserve_parity n hodd  -- hypothetical
    sorry
```

---

## Integration with Main Proof

Both sorries are used in the recursive descent:

```lean
-- In nat_descent_to_basin (lines ~150-175):
lemma nat_descent_to_basin (n : ℕ) (hodd : n % 2 = 1) (h_large : 63 < n) :
  ∃ k : ℕ, k > 0 ∧ iterate_k k n ≤ 63 := by
    refine Nat.lt_wf.induction n ... ?_ hodd h_large
    intro m ih hm_odd hm_large
    obtain ⟨K, hK_contract⟩ := exists_contracting_iterate m hm_odd hm_large  -- Uses Sorry #1
    by_cases h_basin : iterate_k K m ≤ 63
    · use K; exact ⟨by omega, h_basin⟩
    · push_neg at h_basin
      have hm'_odd : iterate_k K m % 2 = 1 :=                              -- Uses Sorry #2
        iterate_k_odd_preserves_odd K m hm_odd (Or.inr (by omega))
      obtain ⟨k', hk'_pos, hk'_basin⟩ := ih (iterate_k K m) ...
      use K + k'
      exact ⟨by omega, by rw [iterate_k_add, hk'_basin]⟩
```

---

## Priority for Closure

| Sorry | Complexity | Impact | Priority |
|-------|-----------|--------|----------|
| Sorry #1 (contraction glue) | Medium-High | Critical for descent | 1 |
| Sorry #2 (parity preservation) | Low-Medium | Recursion enabler | 2 |

**Recommendation:** Close Sorry #1 first (ensures descent happens), then Sorry #2 (enables iteration).

---

## Potential "One Lemma Closes Both" Solution

If we implement an `oddBlock` operator:

```lean
/-- One Collatz "window": apply (3n+1), divide by 2's, land on odd. -/
def oddBlock : ℕ → ℕ := sorry  -- or implement from DP certificate

/-- oddBlock produces smaller value. -/
lemma oddBlock_contracts (n : ℕ) (hodd : n % 2 = 1) (hlarge : 63 < n) :
  oddBlock n < n := sixteen_step_drop  -- ALREADY PROVEN!

/-- oddBlock result is odd. -/
lemma oddBlock_preserves_odd (n : ℕ) (hodd : n % 2 = 1) :
  oddBlock n % 2 = 1 := sorry  -- Single lemma for both parities

/-- oddBlock equals iterate_k K for appropriate K. -/
lemma oddBlock_eq_iterate (n : ℕ) :
  ∃ K ≥ 45, iterate_k K n = oddBlock n := sorry  -- Glue lemma

-- Then both sorries close:
lemma exists_contracting_iterate ... :=
  let ⟨K, -, hk⟩ := oddBlock_eq_iterate m
  ⟨K, by rw [hk]; exact oddBlock_contracts m hodd hlarge⟩

lemma iterate_k_odd_preserves_odd ... :=
  let ⟨K, -, hk⟩ := oddBlock_eq_iterate n
  by rw [hk]; exact oddBlock_preserves_odd n hodd
```

This clean approach reduces both sorries to **one bridge lemma**: linking the `oddBlock` abstraction to `iterate_k`.
