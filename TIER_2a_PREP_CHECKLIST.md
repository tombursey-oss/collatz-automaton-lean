# TIER 2a PREP CHECKLIST

**Before you start Tier 2a, complete this checklist.**

---

## Issue 1: Fix Documentation (edges count)

- [x] Confirmed: `edges.length = 64` (not 42)
- [x] Updated TIER_1_SANITY_CHECK_RESULTS.md
- [x] Updated TIER_1_VERIFICATION_SUMMARY.md
- [x] Created CRITICAL_TIER_1_TO_2_CAVEATS.md

**Status:** ✅ COMPLETE

---

## Issue 2: Understand Decidable ≠ Tractable

- [x] Documented in CRITICAL_TIER_1_TO_2_CAVEATS.md
- [x] Added warning: Tier 3 cannot brute-force 64^16 paths
- [x] Decision: Tier 3 must use DP inside Lean or external certificate

**Status:** ✅ COMPLETE

---

## Issue 3: Identify and Plan Lemma8_DensityFloor.lean Cleanup

**Current state:**
```
src/CollatzAutomaton/Lemma8_DensityFloor.lean (line 79):
  structure PathLen (L : Nat) where
    start : State
    steps : List State           ❌ OLD: state list semantics
    len_eq : steps.length = L

src/CollatzAutomaton/Lemma8_DensityFloor.lean (line 91):
  def window_of_path (p : PathLen L) : Window := by
    ...
    (p.steps.get ⟨i, h⟩).residue % 10  ❌ FATAL BUG
```

**Solution:**

### Step 1: Import Path.lean (NEW)
```lean
import CollatzAutomaton.Path  -- Add this at top of Lemma8_DensityFloor.lean
```

### Step 2: Delete OLD PathLen definition
Remove lines 79–86 (the old structure with steps : List State)

### Step 3: Delete OLD window_of_path definition
Remove lines 91–107 (the old def with residue % 10 bug)

### Step 4: Define new window extractor (Tier 2b)
```lean
-- NEW: Use Path.PathLen with edge list
def windowVals {L : Nat} (p : PathLen L) : List Nat :=
  p.edges.map edgeWeight

lemma windowVals_length {L} (p : PathLen L) : 
  (windowVals p).length = L := by
  simp [windowVals, p.len_eq]
```

**Timeline:** 
- [ ] Before Tier 2a: Delete old definitions
- [ ] During Tier 2b: Define windowVals

---

## Pre-Tier-2a Audit

Run these commands to verify cleanup:

### Audit 1: Only ONE PathLen
```bash
rg -n "structure PathLen" src/CollatzAutomaton
```

**Expected output:**
```
src/CollatzAutomaton/Path.lean:12:structure PathLen (L : Nat) where
```

**Status:** ⏳ PENDING (currently has 2)

### Audit 2: Only ONE weightSum
```bash
rg -n "def weightSum" src/CollatzAutomaton
```

**Expected output:**
```
src/CollatzAutomaton/Path.lean:19:def weightSum {L : Nat} (p : PathLen L) : Nat :=
```

**Status:** ⏳ PENDING (currently has 1, correct)

### Audit 3: window_of_path exists only in Lemma8 (after Tier 2b)
```bash
rg -n "def window_of_path" src/CollatzAutomaton
```

**Expected output (after Tier 2b):**
```
src/CollatzAutomaton/Lemma8_DensityFloor.lean:XX:def windowVals {L : Nat} (p : PathLen L) : List Nat :=
```

**Status:** ⏳ PENDING (currently has 1 old definition to delete)

---

## Tier 2a Implementation Checklist

Once you start Tier 2a:

- [ ] Add `import CollatzAutomaton.Path` to Lemma8_DensityFloor.lean (top of imports)
- [ ] Delete OLD PathLen structure (lines 79–86)
- [ ] Delete OLD window_of_path definition (lines 91–107)
- [ ] Run audit: `rg -n "structure PathLen" src/CollatzAutomaton` → expect 1 match
- [ ] Run audit: `rg -n "def weightSum" src/CollatzAutomaton` → expect 1 match
- [ ] Build: `lake build` → should pass
- [ ] Verify types still work in downstream lemmas
- [ ] Move to Tier 2b once all lemmas compile

---

## Tier 2b Implementation Preview

Once Tier 2a compiles:

- [ ] Define `windowVals` using `PathLen.edges.map edgeWeight`
- [ ] Prove `windowVals_length` lemma
- [ ] Remove any references to old `steps : List State`
- [ ] Verify: `#print axioms windowVals` → should be "(no axioms)"

---

## Tier 3 Strategy Decision

Before starting Tier 3 proofs:

**Choose ONE approach:**

### Option A: DP Inside Lean (Recommended)
- [ ] Implement min-plus matrix multiplication
- [ ] Compute W[k, s, s'] for k=16, all state pairs
- [ ] Verify all entries ≥ 29
- Complexity: Moderate (matrix code) but entirely verifiable

### Option B: External Certificate
- [ ] DP computed externally (Python/C++)
- [ ] Produce invariant: `is_valid_certificate : Cert → Prop`
- [ ] Validate certificate in Lean
- Complexity: Requires trusting external tool, but verification is fast

### Option C: ❌ DO NOT USE
- [ ] ❌ Brute-force enumeration of 64^16 paths
- [ ] ❌ Infeasible computationally
- [ ] ❌ Even with decidability

**Recommendation:** Option A (DP inside Lean) because:
- ✅ Fully verifiable in Lean
- ✅ No external dependencies
- ✅ Moderate complexity
- ✅ Can reuse DP structure later

---

## Final Checklist Before Starting Tier 2a

- [x] Understand: edges.length = 64
- [x] Understand: Decidable ≠ tractable
- [x] Understand: duplicate PathLen must be deleted
- [x] Documentation updated
- [x] Critical caveats document created
- [ ] Ready to start Tier 2a

**Status:** ⏳ READY (once you read the caveats)

---

**Next:** Read [CRITICAL_TIER_1_TO_2_CAVEATS.md](CRITICAL_TIER_1_TO_2_CAVEATS.md) carefully, then start Tier 2a with the cleanup steps above.
