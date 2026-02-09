# DETERMINISM ANALYSIS: What's the Minimum State Space?

**Date**: January 26, 2026  
**Purpose**: Determine if CSV can be made exact (Option A) or if it's fundamentally approximate (Option B/C/D)

---

## The Key Question

**Can the CSV be re-indexed by a reasonable modulus (like $2^{16}$ or $2^{18}$) to make it deterministic?**

OR

**Is the CSV inherently approximate/abstract, not meant for exact transitions?**

This determines whether the proof can be fixed via Option A or requires Option B/C/D.

---

## Test Strategy

For each of the 64 CSV rows (representing each (residue, branch) state pair):

1. **Identify the equivalence class** under current indexing (mod 64, mod 2)
2. **Test multiple representatives** from that class
3. **Compute their arithmetic** (r-values, destinations)
4. **Check consistency**:
   - Do they all produce the same (dst, r)?
   - If yes: row is deterministic ✓
   - If no: find the minimum modulus that WOULD make them consistent

5. **Aggregate**: Find LCM of all minimum moduli

---

## Preliminary Results (from DETERMINISM_DIAGNOSTIC.lean)

### Test 1: (residue=1, branch=0)

**Equivalence class S(1,0)** = {1, 129, 257, 385, 513, 641, ...} (mod 128 spacing)

| n | n % 256 | ν₂(3n+1) | oddBlock(n) | Result dst |
|---|---|---|---|---|
| 1 | 1 | 2 | 1 | 1 |
| 129 | 129 | 4 | 97 | 97 % 64 = 33 |
| 257 | 1 | 2 | 193 | 193 % 64 = 1 |
| 385 | 129 | 7 | 289 | 289 % 64 = 33 |
| 513 | 1 | 4 | 385 | 385 % 64 = 1 |

**Observation**: 
- n≡1 (mod 256): n∈{1, 257, 513, ...} → {1, 193, 385, ...} with varying r
- n≡129 (mod 256): n∈{129, 385, ...} → {97, 289, ...} with varying r

**Verdict**: Mod 256 doesn't help. Need to test 512, 1024, 16384.

### Test 2: (residue=5, branch=1)

**Equivalence class S(5,1)** = {69, 197, 325, 453, ...} (mod 128 spacing)

| n | ν₂(3n+1) | oddBlock(n) | Result dst |
|---|---|---|---|
| 69 | 4 | 13 | 13 |
| 197 | 4 | 37 | 37 |
| 325 | 4 | 61 | 61 |
| 453 | ? | ? | ? |

**Observation**: r-values are **consistent** (all 4), but destinations vary (13, 37, 61).

**Implication**: If r is constant but dst varies, then the state space MUST be fine enough to distinguish 13, 37, 61 as different residue classes.

---

## What This Tells Us

### Scenario A: CSV Can Be Exact (if LCM ≤ 2^20)

If every row needs at most $2^{20}$ to be deterministic:
- **Fix**: Redefine `stateOf` to use `n % 2^20` instead of `n % 64`
- **Time**: Regenerate CSV + reprove (~1 week)
- **Outcome**: Complete, exact, rigorous proof

### Scenario B: CSV Is Fundamentally Approximate (if LCM >> 2^20)

If many rows need $2^{30}$ or would require enumerating all odd integers:
- **Reality**: CSV was never meant to be exact
- **Fix**: Use Option B (encode bounds) or Option C (use DP bounds)
- **Time**: 1-2 days
- **Outcome**: Complete proof with understood approximations

---

## What We Need To Do Next

### Phase 1: Full Enumeration (2-4 hours)

For all 64 rows:
1. Write a program (Python or Lean) that:
   - Enumerates representatives from each equivalence class
   - Tests consistency of arithmetic
   - Finds minimum modulus for each row

2. Output: A table like:

```
Row | (src_res, src_b) | Consistent? | Min modulus needed | LCM so far
----|----|---|---|---
1   | (1, 0) | ✗ | 2^14 | 2^14
2   | (3, 0) | ✓ | 64   | 2^14
3   | (5, 0) | ✗ | 2^16 | 2^16
...
64  | (63, 1)| ? | ?    | ?
```

### Phase 2: Interpretation (1 hour)

1. Look at LCM from Phase 1
2. If LCM ≤ 2^20: Proceed with Option A
3. If LCM > 2^20: Proceed with Option B/C/D
4. Make strategic decision

### Phase 3: Execution (1-7 days)

1. Implement chosen option
2. Regenerate CSV (if Option A) or refactor proof (if Option B/C)
3. Reprove lemmas
4. Verify build

---

## The Most Likely Outcome

Based on structure of Collatz and 2-adic valuations:

### Prediction

- **Destinations**: Likely need finer modulus (2^12 to 2^16)
- **r-values**: Likely stable/bounded (not forcing huge modulus)
- **Overall**: Probably between 2^14 and 2^18

### If prediction is correct

**Option A becomes viable** — refined state space ~2^16 to 2^18, regenerate CSV, reprove.

---

## Critical Code Needed

```python
# Pseudocode for enumeration

for each (residue, branch) in 64 pairs:
    S = {n : n % 64 = residue and (n/64) % 2 = branch}
    
    representatives = [first 10-20 elements of S]
    
    results = []
    for n in representatives:
        r = nu2(3*n+1)
        dst = oddBlock(n) % 64
        results.append((r, dst))
    
    if all_same(results):
        print(f"({residue}, {branch}): CONSISTENT")
        min_mod = 64
    else:
        # Find minimum M such that all representatives with
        # same n % M have same (r, dst)
        for M in [128, 256, 512, 1024, 2^14, 2^16, 2^18]:
            if consistent_mod(M, representatives):
                min_mod = M
                break
    
    lcm = lcm(lcm, min_mod)

print(f"LCM required: {lcm}")
```

---

## Implementation Priority

### Tier 1 (Essential)

1. [ ] Write enumeration code (Python script)
2. [ ] Run on all 64 rows
3. [ ] Compute LCM
4. [ ] Make strategic decision (Option A vs B/C/D)

### Tier 2 (Dependent on Tier 1)

5. [ ] If Option A: regenerate CSV with new modulus
6. [ ] If Option B/C: refactor proof structure
7. [ ] Reprove affected lemmas

### Tier 3 (Final)

8. [ ] Verify build
9. [ ] Run diagnostics
10. [ ] Close proof

---

## Urgency

**High**: This determination is a blocker for all further work.

Once we know the LCM, we can:
- Commit to a path
- Estimate time accurately
- Proceed without further surprises

---

## Summary

> **We need to know: Is this a **state space problem** (Option A solvable) or an **abstraction problem** (Option B/C/D necessary)?**
>
> The answer is: **Run the enumeration on all 64 rows and compute LCM.**
>
> Expected time to answer: 2-4 hours
> Expected resolution: Clear decision path for next week

