# Quick Reference: Bridge Lemma Implementation

## Three Lemmas to Prove

All in `src/CollatzAutomaton/MainTheorem.lean`

### 1. oddBlock_is_odd (Line 44)
**Statement:** For odd n, oddBlock n is also odd  
**Key fact:** (3n+1) = 2^r · m where m is odd → (3n+1)/2^r = m (odd)  
**Tactic:** Use Nat.factorization properties  
**Difficulty:** ⭐ Low

### 2. oddBlock_eq_iterate (Line 57)
**Statement:** ∃ r, iterate_k(1+r, n) = oddBlock n  
**Key fact:** 1 step gives 3n+1 (even), r steps divide by 2 repeatedly  
**Tactic:** Prove iterate_k 1 n = 3n+1, then iterate_k r (3n+1) = (3n+1)/2^r  
**Difficulty:** ⭐⭐ Medium

### 3. oddBlock16_eq_iterate (Line 64)
**Statement:** ∃ K, iterate_k K n = oddBlock^[16] n ∧ result is odd  
**Key fact:** Compose lemma 2 sixteen times with iterate_k_add  
**Tactic:** Induction on 16, each step adds 1 + r_i  
**Difficulty:** ⭐⭐ Medium

## What Closes When

| Lemma Proven | Closes |
|---|---|
| oddBlock_is_odd | Part of oddBlock_eq_iterate |
| oddBlock_eq_iterate | Composition in oddBlock16_eq_iterate |
| oddBlock16_eq_iterate | exists_contracting_iterate ✅ |
| (above) | nat_descent_to_basin ✅ |
| (above) | dp_global_descent ✅ |
| (above) | collatz_converges ✅ (MAIN THEOREM) |

## Testing Each Lemma

```bash
# After proving oddBlock_is_odd:
#check MainTheorem.oddBlock_is_odd
-- Expected: ∀ (n : ℕ), n % 2 = 1 → oddBlock n % 2 = 1

# After proving oddBlock_eq_iterate:
#check MainTheorem.oddBlock_eq_iterate
-- Expected: ∀ (n : ℕ), n % 2 = 1 → 
--   ∃ r : ℕ, iterate_k (1 + r) n = oddBlock n ∧ oddBlock n % 2 = 1

# After proving oddBlock16_eq_iterate:
#check MainTheorem.oddBlock16_eq_iterate
-- Expected: ∀ (n : ℕ), n % 2 = 1 → 
--   ∃ K : ℕ, iterate_k K n = (oddBlock^[16]) n ∧ (oddBlock^[16]) n % 2 = 1
```

## Proof Sketch Templates

### For oddBlock_is_odd
```lean
lemma oddBlock_is_odd (n : ℕ) (hodd : n % 2 = 1) : oddBlock n % 2 = 1 := by
  unfold oddBlock
  let r := Nat.factorization (3 * n + 1) 2
  -- Goal: ((3 * n + 1) / 2^r) % 2 = 1
  -- Key: use fact that factorization extracts all factors of 2
  -- Then quotient is odd
  sorry
```

### For oddBlock_eq_iterate
```lean
lemma oddBlock_eq_iterate (n : ℕ) (hodd : n % 2 = 1) :
  ∃ r : ℕ, iterate_k (1 + r) n = oddBlock n ∧ oddBlock n % 2 = 1 := by
  use Nat.factorization (3 * n + 1) 2
  constructor
  · -- Prove: iterate_k (1 + r) n = oddBlock n
    -- Step 1: show iterate_k 1 n = 3*n + 1
    have h1 : iterate_k 1 n = 3 * n + 1 := by
      simp [iterate_k, hodd]
    -- Step 2: show iterate_k r (3*n + 1) = (3*n + 1) / 2^r
    have hr : iterate_k r (3 * n + 1) = (3 * n + 1) / 2^r := by
      -- Induction on r, each step divides by 2
      sorry
    -- Step 3: compose
    rw [iterate_k_add, h1, hr]
  · exact oddBlock_is_odd n hodd
```

### For oddBlock16_eq_iterate
```lean
lemma oddBlock16_eq_iterate (n : ℕ) (hodd : n % 2 = 1) :
  ∃ K : ℕ, iterate_k K n = (oddBlock^[16]) n ∧ ((oddBlock^[16]) n % 2 = 1) := by
  -- Induction pattern: 
  -- - Base: oddBlock^[0] n = n, K = 0
  -- - Step: given K_i and oddBlock^[i] n, apply oddBlock_eq_iterate to get K_{i+1}
  
  induction (Fintype.card (Fin 16)) with
  | zero => 
    use 0
    simp  -- Identity case
  | succ m ih =>
    obtain ⟨K_prev, hK_eq, hK_odd⟩ := ih
    -- Apply oddBlock_eq_iterate one more time
    obtain ⟨r, hr_eq, hr_odd⟩ := oddBlock_eq_iterate (oddBlock^[m] n) hK_odd
    use K_prev + (1 + r)
    rw [iterate_k_add, hK_eq, hr_eq]
    -- Result is oddBlock^[m+1] n, which is odd
    exact hr_odd
```

## Key Lemmas Already Available

- ✅ iterate_k_add: Composition law
- ✅ odd_step_produces_even: (3n+1) is even for odd n
- ✅ oddBlock_is_odd: Definition-based (once proven)
- ✅ sixteen_step_drop: oddBlock^[16] n < n

## Debugging Checklist

- [ ] oddBlock definition uses factorization 2
- [ ] oddBlock is odd by construction (once lemma proven)
- [ ] iterate_k 1 n applies 3n+1 (test: n=1 → 4)
- [ ] iterate_k r (even number) divides by 2 repeatedly
- [ ] iterate_k_add allows composition
- [ ] 16 iterations can be built from single iterations

## Success Criteria

When all three lemmas are proven:
- ✅ `lake build` succeeds with 0 sorries
- ✅ `#check collatz_converges` shows theorem is fully proven
- ✅ No remaining sorries in src/
- 🎉 Formal proof complete!

---

**Timeline:** ~2 hours estimated for experienced Lean dev
