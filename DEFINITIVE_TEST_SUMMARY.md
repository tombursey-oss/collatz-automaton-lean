# THE DEFINITIVE TEST: Minimum State Space for Determinism

**Date**: January 26, 2026  
**Status**: Ready to execute  
**Purpose**: Answer the core design question  
**Time to run**: ~2 minutes  
**Time to interpret**: ~10 minutes  

---

## The Question We're Answering

> **Can the CSV be made deterministic with a reasonable state space (≤2^20)?**
>
> If YES → Option A is viable (refine state space, ~1 week)  
> If NO → Options B/C/D required (use bounds, ~1-3 days)

---

## How The Test Works

### Step 1: For Each CSV Row
For each (residue, branch) pair representing a state:

```
S(r,b) = {n odd : n ≡ r (mod 64) and (n/64) ≡ b (mod 2)}
```

**Example**: S(21,1) = {85, 213, 341, 469, 597, ...}

### Step 2: Test Consistency
For 30 representatives in S(r,b), compute:
- r-value: ν₂(3n+1)
- Destination: stateOf(oddBlock(n))

**Question**: Do they all produce the same (r-value, destination)?

### Step 3: Find Minimum Modulus
If NOT consistent at mod 64, find minimum M such that they ARE consistent at mod M.

**Example**:
- Mod 64: inconsistent (85 gives r=8, 213 gives r=7)
- Mod 256: inconsistent
- Mod 16384: consistent ✓
- Min modulus: 2^14 = 16384

### Step 4: Aggregate
Compute LCM of all 64 minimum moduli.

**Result**: The minimum state space size needed for full determinism.

---

## The Diagnostic Script

**File**: `determinism_check.py`

**Run**:
```bash
python3 determinism_check.py
```

**Output**: Table showing for each row:
- Consistent with mod 64? (✓ or ✗)
- If ✗: minimum modulus needed
- LCM of all minimums
- Recommendation

---

## What The Results Mean

### Scenario 1: LCM = 64

All rows already consistent!

**Status**: Current 64-state automaton is determinstic (but it's not—contradiction!)  
**Interpretation**: Something else is wrong (maybe CSV data issue, not state space)  
**Action**: Investigate CSV generation

### Scenario 2: LCM ≤ 2^16 (65536)

State space needs refinement to 2^16 or similar.

**Status**: **OPTION A IS VIABLE** ✓  
**Action**: 
1. Redefine stateOf(n) to use n % LCM
2. Regenerate CSV (write script or do by hand)
3. Reprove lemmas (mostly automatic)
4. **Time**: ~1 week

### Scenario 3: 2^16 < LCM ≤ 2^20

State space needs refinement to 2^18-2^20.

**Status**: **OPTION A IS MARGINAL** ⚠  
**Action**: 
- If CSV generation is automated: Option A (2 weeks)
- If CSV generation is manual: Consider Option B/C (1-3 days)

### Scenario 4: LCM > 2^20

State space would need to be prohibitively large.

**Status**: **OPTION A IS NOT VIABLE** ✗  
**Action**: CSV is not meant to be exact
1. Accept it as approximate/abstract
2. Use Option B (encode bounds in Lean)
3. Or Option C (use DP lower bounds)
4. **Time**: 1-3 days

---

## Why This Test Is Definitive

**Previous diagnostic** (SURGICAL_DIAGNOSTIC.lean):
- Proved one row is inconsistent ✓
- But didn't tell us if it's fixable

**This test**:
- Tests ALL 64 rows
- Computes the minimum fix needed
- Tells us EXACTLY what's required
- **This is the decision point**

---

## After The Test

### If Option A Viable

**1. Redefine the state space** (1 hour)
```lean
-- Old:
def stateOf (n : Nat) : State :=
  { residue := n % 64, branch := (n / 64) % 2 = 1 }

-- New (if LCM = 2^16):
def stateOf (n : Nat) : State :=
  { residue := n % 65536, branch := ... }
```

**2. Regenerate CSV** (2-4 hours)
- For each of potentially 2^16 states, compute transitions
- Or: verify existing CSV is correct and just reindex

**3. Reprove key lemmas** (4-8 hours)
- stateOf_StateOK (trivial with new definition)
- oddBlock16_eq_iterate (still works)
- step_edge (now provable!)

**4. Full build** (1-2 hours)
- Lake build with new definitions
- Run tests

**Total**: ~1 week

### If Option A NOT Viable

**1. Use Option B: Bounds in Lean** (2-4 days)
```lean
-- Instead of proving exact step_edge:
lemma step_edge_lower_bound (n : Nat) :
  ∃ e ∈ edges, e.w ≥ arithWeight n / 2
```

**2. Or use Option C: DP bounds** (1-3 days)
Accept the CSV as providing lower bounds for DP analysis.

**Total**: 1-3 days

---

## Critical Path

```
Now → Run determinism_check.py → 2 min
       ↓
       Interpret LCM result → 10 min
       ↓
    ┌──────────────────────────────┬──────────────────────┐
    ↓ (if LCM ≤ 2^20)              ↓ (if LCM > 2^20)     ↓ (if LCM = 64)
Option A viable              Option B/C needed      Investigate CSV
1 week                       1-3 days               Unknown
Regenerate CSV               Use bounds             Could be design flaw
```

---

## Go/No-Go Criteria

### When To Execute Test

**Now**. This is the most important diagnostic remaining.

### When To Use Results

After the test completes (2-10 minutes), we have complete clarity on next steps.

### When To Start Implementation

After choosing Option A/B/C/D and planning the work (same day as test).

---

## The Real Value

> **After this test runs, we will KNOW:**
>
> - Is the CSV intended to be exact? (If LCM ≤ 2^20)
> - Is the CSV meant to be approximate? (If LCM > 2^20)
> - Is something more fundamentally wrong? (If LCM = 64, contradiction)
>
> **We will NOT be guessing anymore.**

---

## Summary

| What | Value | 
|------|-------|
| **Test name** | determinism_check.py |
| **What it tests** | Minimum state space for full determinism |
| **Time to run** | ~2 minutes |
| **Decision made** | Which of 4 resolution paths to take |
| **Impact** | Unblocks entire project for implementation |
| **Confidence** | Very high (mathematical, not heuristic) |
| **Next step** | Run test, interpret results, execute path |

---

**Next action**: Run `python3 determinism_check.py` and report LCM result.

