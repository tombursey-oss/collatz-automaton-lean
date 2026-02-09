# How To Run The Determinism Check

**Goal**: Automatically find the minimum modulus needed to make all 64 CSV rows deterministic.

**Time**: ~2 minutes to run

**Output**: Clear recommendation on whether Option A (refine state space) is viable

---

## Quick Start

```bash
# From workspace root
python3 determinism_check.py
```

## What It Does

1. **For each of 64 CSV rows** (all (residue, branch) pairs):
   - Generates 30 representatives from the equivalence class
   - Computes arithmetic (r-value, destination) for each
   - Tests: "Are they consistent mod 64?"
   - If no: finds minimum modulus that WOULD make them consistent

2. **Computes LCM** across all 64 rows

3. **Outputs**:
   - Table of results
   - Summary statistics
   - Recommendation (Option A viable? or not?)

---

## Expected Output Format

```
==================================================
DETERMINISM DIAGNOSTIC
==================================================

Testing ( 0, 0)... ✓ CONSISTENT        min_mod = 2^ 6 (    64)
Testing ( 1, 0)... ✗ NEEDS LARGER      min_mod = 2^14 ( 16384)
Testing ( 2, 0)... ✓ CONSISTENT        min_mod = 2^ 6 (    64)
...
Testing (63, 1)... ✗ NEEDS LARGER      min_mod = 2^16 ( 65536)

==================================================
SUMMARY
==================================================

Rows consistent with mod 64:        12 / 64
Rows requiring larger modulus:      52 / 64

LCM of all min moduli:              2^16 = 65536

✓ OPTION A (Refine state space) is VIABLE
  The state space needs only 2^16 (65536 states)
  This is manageable. Estimate: ~1 week to regenerate CSV and reprove.

==================================================
DETAILED RESULTS BY MIN_MODULUS
==================================================

Min modulus 2^ 6 (    64): 12 rows
  Pairs: [(1, 0), (3, 0), (5, 0), ...]

Min modulus 2^14 ( 16384): 28 rows
  Pairs: [(21, 1), (25, 1), ...]

Min modulus 2^16 ( 65536): 24 rows
  Pairs: [(13, 0), (27, 0), ...]
```

---

## Interpreting Results

### If LCM ≤ 2^16 (65536)

✓ **OPTION A IS VIABLE**

The CSV can be made deterministic by using a state space of size 2^16 or 2^18.

**Next steps**:
1. Run determinism_check.py to get exact LCM
2. Redefine stateOf to use `n % LCM` instead of `n % 64`
3. Regenerate CSV with new indexing
4. Reprove lemmas (mostly automatic)
5. Build complete proof

**Estimated time**: 1-2 weeks

### If LCM ≤ 2^20 (1048576)

⚠ **OPTION A IS MARGINAL**

Technically viable, but large state space may have practical issues.

**Alternative**: Consider Option B (encode bounds) if CSV regeneration seems costly.

### If LCM > 2^20

✗ **OPTION A IS NOT VIABLE**

The state space would be too large for determinism to be achievable this way.

**Next steps**:
1. Accept that CSV is approximate, not exact
2. Interpret it as a lower bound on path weights
3. Use Option B (DP bounds) or Option C (relaxed proof)
4. Proceed with current 64-state structure
5. Proof is valid but weaker

**Estimated time**: 1-3 days

---

## Troubleshooting

### Python not found

```bash
# Try python instead of python3
python determinism_check.py
```

### Script hangs

- Increase timeout or reduce num_representatives (line in find_representatives)
- The script shouldn't hang; if it does, report the issue

### Unexpected results

- Verify the nu2() and oddBlock() functions match Lean definitions
- Check that stateOf() matches Graph.lean

---

## Next Session Agenda

1. [ ] Run determinism_check.py
2. [ ] Document LCM result
3. [ ] Make decision: Option A or B/C/D
4. [ ] Schedule implementation (1-7 days depending on choice)

---

## Key Insight

> This script answers the **crucial design question**: 
>
> "Is the CSV a finite automaton that just needs reindexing, 
>  or is it fundamentally an approximation?"
>
> The answer determines which of 4 resolution paths is correct.

