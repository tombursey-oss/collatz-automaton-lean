# Lemma 3: Exact Statement — weightSum Equality

## The Assertion

**Location:** [TIER_2c_ROADMAP.md](TIER_2c_ROADMAP.md#L243-L250)

**Theorem Statement (Lean):**

```lean
theorem weightSum_eq_valSum (L : Nat) (n : Nat) (hodd : n % 2 = 1) :
  weightSum (trajectoryPath L n) = 
    (List.range L).foldl (fun acc i => acc + arithWeight (arithIter i n)) 0
```

## English Interpretation

**For any odd integer n and any path length L:**

The sum of edge weights in the graph path derived from n's arithmetic trajectory 
**exactly equals** the sum of arithmetic weights over L steps.

This is **exact equality (=)**, not an inequality (≥ or ≤).

## Components Explained

### Left Side: `weightSum (trajectoryPath L n)`
- `trajectoryPath L n`: Construct the graph path by lifting the arithmetic sequence into the automaton
- `weightSum p`: Sum of all edge weights in path p

### Right Side: `(List.range L).foldl (fun acc i => acc + arithWeight (arithIter i n)) 0`
- `List.range L`: [0, 1, 2, ..., L-1]
- `arithIter i n`: The i-th iterate of the Collatz function starting from n
  ```lean
  def arithIter : Nat → Nat → Nat
    | 0, n => n
    | i+1, n => arithIter i (arithStep n)
  ```
- `arithWeight`: The 2-adic valuation (ν₂) at each step
- The fold: `acc₀ = 0; acc₁ = acc₀ + arithWeight(n); acc₂ = acc₁ + arithWeight(arithStep n); ...`

## Why This Matters

This lemma is the **semantic bridge** connecting:
- **Graph world:** Path edges with computed weights
- **Arithmetic world:** 2-adic valuations of Collatz iterates

Without this equality, the DP bound proven on graph windows cannot be transferred 
to actual Collatz trajectories.

## Proof Strategy

**Location:** [TIER_2c_ROADMAP.md](TIER_2c_ROADMAP.md#L258-L278)

Induction on L:

```lean
theorem weightSum_eq_valSum (L : Nat) (n : Nat) (hodd : n % 2 = 1) :
  weightSum (trajectoryPath L n) = 
    (List.range L).foldl (fun acc i => acc + arithWeight (arithIter i n)) 0 := by
  induction L with
  | zero =>
    simp [trajectoryPath, arithIter, weightSum]
  | succ L' ih =>
    simp [trajectoryPath, arithIter, weightSum]
    rw [List.range_succ]
    -- Use step_edge to show the edge weight matches arithWeight
    have : (trajectoryPath (L'+1) n).edges |>.head!.w = arithWeight n := by
      -- Extracted edge from step_edge has weight arithWeight n
      sorry
    rw [this]
    rw [← ih]
    ring
```

**Key step:** At each inductive step, use `step_edge` lemma to extract the 
edge from state `stateOf(n)` to `stateOf(arithStep(n))` and verify its weight 
equals `arithWeight(n)`.

## Current Status

- ✅ **Statement exists** in TIER_2c_ROADMAP.md
- ❌ **Proof not implemented** in actual Lean code
- 🔴 **This is the critical missing lemma** that blocks the semantic bridge

## Related Lemmas

- **Lemma 1 (window_encoding_identity):** Window structure preserves length
- **Lemma 2 (sum_decomposition):** valuation_sum correctly folds window values  
- **Lemma 3 (THIS ONE):** weightSum = arithmetic weight sum (MISSING)
- **Lemma 4:** DP coverage and density floor

## Action Required

To complete the proof, implement `weightSum_eq_valSum` with the inductive 
strategy shown above. This depends on:

1. ✅ `trajectoryPath` function existing
2. ✅ `arithIter` function existing
3. ✅ `arithWeight` function existing (should be ν₂)
4. ❌ **`step_edge` lemma** — This is also missing and blocks Lemma 3
5. ❌ Implementation of the inductive proof

---

**NOTE:** The determinism diagnostic revealed that `step_edge` is currently 
impossible to prove because the state space (mod 64) is too coarse. 
See [DETERMINISM_ANALYSIS_PLAN.md](DETERMINISM_ANALYSIS_PLAN.md) for the 
required state space refinement to 2^12.
