# CRITICAL FINDING: CSV Data Inconsistency Diagnosed

**Date**: January 26, 2026  
**Status**: 🚨 **RED FLAG 1 IS WORSE THAN THOUGHT**

---

## The Surgical Test

We tested the claim: "For a fixed (src_residue, src_b) pair, is the (dst, r_val) constant?"

**Test case**: (src_residue = 21, src_b = 1)

### Definition of S(21, 1)

With `stateOf(n) = (n % 64, (n / 64) % 2 = 1)`:

$$S(21,1) = \{n \text{ odd} : n \equiv 21 \pmod{64} \text{ and } (n/64) \bmod 2 = 1\}$$

Algebraically:
- $n = 64k + 21$ where $k$ is odd
- $k = 2m + 1 \Rightarrow n = 128m + 85$
- **Result**: $S(21,1) = \{85, 213, 341, 469, 597, \ldots\}$ (arithmetic sequence with difference 128)

### Test Results

| $n$ | $3n+1$ | $\nu_2(3n+1)$ | $\text{oddBlock}(n)$ | CSV $r$ | CSV dst | Match? |
|---|---|---|---|---|---|---|
| 85 | 256 | 8 | 1 | 8 | 1 | ✓ |
| 213 | 640 | **7** | 5 | 8 | 1 | ✗✗ |
| 341 | 1024 | **10** | 1 | 8 | 1 | ✗ |
| 469 | 1408 | **7** | 11 | 8 | 1 | ✗✗ |

### Verdict: 🚨 FAILURE

**The CSV claims $r = 8$ for all entries with (src_residue=21, src_b=1).**  
**But $\nu_2(3n+1)$ varies across $S(21,1)$: {8, 7, 10, 7, ...}**

---

## What This Means

### Hypothesis 1: CSV is indexed by a finer modulus

Maybe the CSV is NOT indexed by $(residue, branch)$ but by $(n \bmod M)$ for some larger $M$?

**Test**: Is there a modulus $M$ such that each row in the CSV corresponds to a single residue class mod $M$?

**Problem**: We've already shown that within $S(21,1)$, different representatives $n$ produce different values of $(r, \text{oddBlock})$. Even if we use a finer modulus for the source, the destination and weight must still be constant on each destination equivalence class.

**Reality check**:
- $n = 85 \mapsto (dst=1, r=8)$
- $n = 213 \mapsto (dst=5, r=7)$

These are in the SAME (residue, branch) class but map to DIFFERENT destinations with DIFFERENT weights.

### Hypothesis 2: CSV is correct but semantics are different

Maybe the CSV row doesn't represent "all n with this (residue, branch)" but rather "a specific representative n"?

**Problem**: Then how do we interpret the edge in the automaton? If an edge only applies to one specific $n$-value, there are infinitely many Collatz trajectories and only finitely many CSV rows — the graph can't be complete.

### Hypothesis 3: CSV is a projection or approximation

Maybe the CSV aggregates multiple arithmetic steps into one "super-edge"? And the edge weight is something other than $\nu_2(3n+1)$?

**Problem**: This contradicts the RED_FLAG_1_RESOLUTION.md document which explicitly states $r$ is the 2-adic valuation.

---

## The Real Issue

**The CSV data, as currently indexed by (residue, branch), cannot represent a deterministic automaton where:**
- Each state has a well-defined outgoing edge
- The edge weight equals $\nu_2(3n+1)$
- The destination is $\text{stateOf}(\text{oddBlock}(n))$

**Because**: Different odd integers $n$ with the same $(n \bmod 64, (n/64) \bmod 2)$ produce different oddBlock results and different 2-adic valuations.

---

## What Needs To Happen

1. **Clarify the CSV semantics**
   - Is each row indexed by a specific residue class mod $M$ for some $M > 64$?
   - Or does each row represent an average/bound rather than an exact value?
   - Or is the CSV derived from a different automaton structure?

2. **Reconcile with stateOf**
   - If $(residue, branch)$ doesn't uniquely determine the next state, what does?
   - The "branch" variable as currently defined is insufficient.

3. **Define the actual state space**
   - Maybe states should be $n \bmod 2^{16}$? Or $n \bmod 2^{14}$?
   - Or the state should include additional information?

---

## Code Evidence

See [SURGICAL_DIAGNOSTIC.lean](SURGICAL_DIAGNOSTIC.lean) for verified computations of:
- $\nu_2(3 \cdot 85 + 1) = 8$, $\text{oddBlock}(85) = 1$
- $\nu_2(3 \cdot 213 + 1) = 7$, $\text{oddBlock}(213) = 5$
- $\nu_2(3 \cdot 341 + 1) = 10$, $\text{oddBlock}(341) = 1$
- $\nu_2(3 \cdot 469 + 1) = 7$, $\text{oddBlock}(469) = 11$

All proven via `decide` (machine-verified).

---

## Implication for Proof

**Current status**: The "90% complete" assessment is overstated because:

- ❌ The semantic bridge (step_edge lemma) cannot be proven
- ❌ The automaton structure doesn't match Collatz arithmetic as defined
- ❌ The CSV data is inconsistent with (residue, branch) indexing

**Required action**: Either:
1. **Redefine stateOf** to use a finer modulus that makes the CSV data consistent, OR
2. **Redefine the CSV** to actually be deterministic given the current stateOf definition

This is not a small fix — it's a structural redesign question.

---

## Summary

| Question | Answer | Status |
|----------|--------|--------|
| Is CSV indexed by (residue, branch)? | ❌ No | DISPROVEN |
| Are (dst, r_val) constant on S(21,1)? | ❌ No | PROVEN CONSTANT |
| Can step_edge lemma be proven? | ❌ No | BLOCKED |
| Does automaton determinism hold? | ❌ No | VIOLATED |

**Recommendation**: Do NOT proceed with implementing step_edge until the CSV semantics are clarified.

