# RED FLAG 1 DEEP ANALYSIS: The Inconsistency Exposed

**Date**: January 26, 2026  
**Severity**: 🔴 **BLOCKS ENTIRE PROOF**

---

## Executive Summary

**The CSV data (ExpandedEdgesV2) cannot be indexed by (residue, branch) = (n % 64, (n/64) % 2).**

We proved this by testing a single edge: (src_residue=21, src_b=1) from the CSV.

- The preimage set $S(21,1) = \{85, 213, 341, 469, ...\}$ (arithmetic sequence mod 128)
- For each representative, we computed the **actual** Collatz arithmetic
- **Result**: Different representatives produce different weights and destinations
- **CSV claims**: All should have weight 8 and destination 1
- **Reality**: Weights are {8, 7, 10, 7, ...}, destinations are {1, 5, 1, 11, ...}

**Conclusion**: The CSV indexing is fundamentally broken as currently used.

---

## Mathematical Details

### Setup

Define:
$$\text{stateOf}(n) := (n \bmod 64, \lfloor n / 64 \rfloor \bmod 2)$$

For a fixed state $(s, b)$:
$$S(s,b) := \{n \in \text{odd} : \text{stateOf}(n) = (s, b)\}$$

For $(s, b) = (21, 1)$:
- Condition: $n \equiv 21 \pmod{64}$ AND $(n \div 64)$ is odd
- Algebra: $n = 64(2k+1) + 21 = 128k + 85$ for $k \geq 0$
- **Set**: $S(21,1) = \{85, 213, 341, 469, 597, 725, 853, ...\}$

### Tested Representatives

For each $n \in S(21,1)$, compute:
- $\nu_2(3n+1)$ = 2-adic valuation
- $\text{oddBlock}(n) := (3n+1) / 2^{\nu_2(3n+1)}$
- $\text{nextState}(n) := \text{stateOf}(\text{oddBlock}(n))$

#### $n = 85$

```
3 × 85 + 1 = 256 = 2⁸ × 1
ν₂(256) = 8
oddBlock(85) = 256 / 256 = 1
stateOf(1) = (1 % 64, (1 / 64) % 2) = (1, 0)

Result: (dst=1, r=8)
CSV claims: (dst=1, r=8) ✓ MATCH
```

#### $n = 213$

```
3 × 213 + 1 = 640 = 2⁷ × 5
ν₂(640) = 7
oddBlock(213) = 640 / 128 = 5
stateOf(5) = (5 % 64, (5 / 64) % 2) = (5, 0)

Result: (dst=5, r=7)
CSV claims: (dst=1, r=8) ✗✗ MISMATCH
```

#### $n = 341$

```
3 × 341 + 1 = 1024 = 2¹⁰ × 1
ν₂(1024) = 10
oddBlock(341) = 1024 / 1024 = 1
stateOf(1) = (1, 0)

Result: (dst=1, r=10)
CSV claims: (dst=1, r=8) ✗ MISMATCH (weight differs)
```

#### $n = 469$

```
3 × 469 + 1 = 1408 = 2⁷ × 11
ν₂(1408) = 7
oddBlock(469) = 1408 / 128 = 11
stateOf(11) = (11, 0)

Result: (dst=11, r=7)
CSV claims: (dst=1, r=8) ✗✗ MISMATCH
```

### Summary Table

| $n$ | $n \bmod 128$ | $3n+1$ | $\nu_2$ | $\text{oddBlock}$ | Actual next state | CSV next state | Weight match? |
|---|---|---|---|---|---|---|---|
| 85 | 85 | 256 | 8 | 1 | (1, 0) | (1, 0) | ✓ |
| 213 | 85 | 640 | 7 | 5 | (5, 0) | (1, 0) | ✗ |
| 341 | 85 | 1024 | 10 | 1 | (1, 0) | (1, 0) | ✗ |
| 469 | 85 | 1408 | 7 | 11 | (11, 0) | (1, 0) | ✗ |

**Observation**: Elements of $S(21,1)$ that are $\equiv 85 \pmod{128}$ produce **different** next states and weights within the set itself.

---

## Root Cause Analysis

### Why Does This Happen?

The 2-adic valuation $\nu_2(3n+1)$ is **NOT** a function of $(n \bmod 64, (n/64) \bmod 2)$.

**Example**: $n = 85$ and $n = 341$ have the same $(n \bmod 64, (n/64) \bmod 2) = (21, 1)$, but:
- $\nu_2(3 \cdot 85 + 1) = 8$
- $\nu_2(3 \cdot 341 + 1) = 10$

### Why Doesn't a Finer Modulus Help?

Could we use $(n \bmod M)$ for some $M > 64$?

**Test**: $(n \bmod 256)$
- $85 \bmod 256 = 85 \mapsto (dst=1, r=8)$
- $341 \bmod 256 = 85 \mapsto (dst=1, r=10)$ ← **Same residue, different weight!**

So even mod 256 doesn't work for the weight.

**Reality**: The valuations $\nu_2(3 \cdot 85 + 1) = 8$ and $\nu_2(3 \cdot 341 + 1) = 10$ will never be the same because they depend on different arithmetic properties.

---

## What the CSV Actually Is

### Hypothesis A: CSV represents a specific modulus class

If the CSV is meant to represent one entry per residue class mod $M$, then $M$ must satisfy:
- For all $n, n'$ with $n \equiv n' \pmod{M}$: $\nu_2(3n+1) = \nu_2(3n'+1)$

**Theorem** (conjecture): There is NO such $M$ that works for all edges because:
- The 2-adic valuation is a non-periodic function
- No finite modulus can make it periodic

### Hypothesis B: CSV is a lower bound or average

Maybe each CSV row represents:
- The MINIMUM weight achievable on the equivalence class?
- The AVERAGE weight?
- The weight for one specific $n$-value?

**Problem**: None of these make sense for a deterministic automaton proof. We need exact weights, not bounds or averages.

### Hypothesis C: CSV is derived from a different automaton

Maybe the CSV comes from a different definition of state space or transition?

**Evidence for this**: The RED_FLAG_1_RESOLUTION.md document suggests using a "branch" variable to encode $\lfloor n / 64 \rfloor \bmod 2$, but this branch is insufficient to determine the next state uniquely (as we've now proven).

---

## Impact on Proof Status

### Current Claims

From FINAL_STATUS_REPORT.md:
- ✅ "Main theorem proven: 0 sorries"
- ✅ "Axioms: 0/4 retired"
- ✅ "DP integration: 2 focused sorries (glue lemmas)"

### Actual Status

- ❌ **Semantic bridge (step_edge) is IMPOSSIBLE to prove** given current definitions
- ❌ **The automaton structure does NOT match Collatz arithmetic**
- ❌ **CSV data is internally inconsistent**
- ⚠️  **"90% complete" is an overestimate**

### Why This Breaks the Proof

The proof structure is:
```
collatz_converges (THEOREM)
  ├─ Basin case (n ≤ 63): uses computed list ✓
  ├─ Large case (n > 63): uses dp_global_descent
  │   └─ dp_global_descent: uses nat_descent_to_basin
  │       └─ nat_descent_to_basin: uses well-founded induction + exists_contracting_iterate
  │           └─ exists_contracting_iterate: uses oddBlock16_eq_iterate
  │               └─ oddBlock16_eq_iterate: uses oddBlock_eq_iterate
  │                   └─ oddBlock_eq_iterate: assumes step_edge works
```

The link to `step_edge` is **broken** because the semantic bridge doesn't exist.

---

## Resolution Paths

### Option 1: Redefine the state space

Change `stateOf(n)` to use a finer modulus, such that:
$$\text{stateOf}(n) = (n \bmod 2^{14}, \ldots)$$

**Advantages**:
- If chosen correctly, CSV data might become consistent
- Proof structure remains the same

**Disadvantages**:
- Requires recomputing all CSV edges
- May make the state space too large for verification
- Unclear what the right modulus is

### Option 2: Redefine edges as bounds/aggregations

Change the interpretation:
- Edge weight becomes an **upper bound** on individual $\nu_2(3n+1)$ values
- Or edge weight is the **maximum** within the equivalence class

**Advantages**:
- Doesn't require recomputing CSV

**Disadvantages**:
- Proof becomes weaker (loose bounds)
- Loses exactness needed for convergence proof

### Option 3: Use a different representation entirely

Instead of (residue, branch), use:
- The $n$-value itself (not modular)
- A tree of states partitioned by prefix of binary representation
- Some other automaton structure

**Advantages**:
- Might be more natural for Collatz

**Disadvantages**:
- Requires complete redesign
- Years of work wasted

---

## Verification Code

See [SURGICAL_DIAGNOSTIC.lean](SURGICAL_DIAGNOSTIC.lean) for:
- Verified computation of $\nu_2(3n+1)$ for $n \in \{85, 213, 341, 469\}$
- Verified computation of $\text{oddBlock}(n)$ for each
- Proof that $\text{stateOf}$ produces the claimed states
- All via `decide` tactic (machine-verified)

---

## Recommendations

### Immediate

1. **Do NOT attempt to implement step_edge**
   - It cannot be proven with current definitions
   - Time will be wasted on an impossible task

2. **Investigate CSV generation**
   - How was the CSV computed originally?
   - What modulus/algorithm was used?
   - Are there additional constraints not documented?

3. **Clarify the automaton semantics**
   - What is the intended state space?
   - How should edges be indexed?
   - What is the relationship to Collatz arithmetic?

### Medium-term

4. **Redefine stateOf or CSV** (not both)
   - One must change; the other must be validated

5. **Reprove key lemmas** (if needed)
   - oddBlock_eq_iterate (lemma 1.1)
   - oddBlock16_eq_iterate (composition)
   - dp_global_descent (if using new state space)

6. **Re-validate basin data**
   - Check basin_rows_reach_1_data still compiles
   - Might need recomputation

### Long-term

7. **Complete the proof**
   - Once state space is defined consistently
   - Implement step_edge with new definition
   - Finish proof bridge

---

## Conclusion

**The proof is architecturally sound but semantically broken.**

The CSV data and the `stateOf` definition are **incompatible** — they don't form a consistent automaton that matches Collatz arithmetic.

**Before ANY further implementation, this mismatch must be resolved.**

Recommended action: Hold a design review to clarify:
1. What the intended automaton structure is
2. How the CSV was derived
3. What the semantics of (residue, branch) actually are

Without this clarity, **no proof is possible**.

