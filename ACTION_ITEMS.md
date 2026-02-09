# ACTION ITEMS — What You Need To Do Next

## Immediate Actions (Today/Tomorrow)

### 1. Resolve Git Network Issue
**Status:** Blocks `lake build` verification  
**Action:** Fix the git remote or use local mathlib cache
```bash
cd c:\collatz_automaton

# Option A: Reconfigure git remote
git remote set-url origin https://github.com/leanprover-community/mathlib4

# Option B: Use local packages only (if already cached)
lake clean
lake build
```

**Verification:** Should see "Build completed successfully"

---

### 2. Clean Lemma8_DensityFloor.lean
**Status:** Required before Tier 2b implementation  
**Action:** Delete OLD definitions that will conflict with new Path.lean

Edit [src/CollatzAutomaton/Lemma8_DensityFloor.lean](src/CollatzAutomaton/Lemma8_DensityFloor.lean):

#### Step 2a: Delete OLD PathLen (lines 79-86)
```lean
-- DELETE THESE LINES:
structure PathLen (L : Nat) where
  steps : List State
  edge_count : steps.length - 1 = L
  -- ... rest of old definition ...
  -- (approx 7 lines total)
```

#### Step 2b: Delete OLD window_of_path (lines 91-107)
```lean
-- DELETE THESE LINES:
def window_of_path : ... :=
  -- ... THE ENTIRE OLD DEFINITION ...
  -- (approx 17 lines with the residue % 10 bug)
```

#### Step 2c: Add Import at Top
Add this line after other imports in Lemma8_DensityFloor.lean:
```lean
import CollatzAutomaton.Path
```

**Verification:** File should have no duplicate definitions

---

## Tier 2b Implementation (1-2 hours)

### 3. Add windowVals Definition

In Lemma8_DensityFloor.lean, add:

```lean
/-- Extract the window (edge weights) from a valid path. -/
def windowVals {L : Nat} (p : PathLen L) : List Nat :=
  p.edges.map edgeWeight
```

**Verification:**
```lean
#check windowVals
-- Should have type: ∀ {L : Nat}, PathLen L → List Nat

#print axioms windowVals
-- Should show: (no axioms)
```

### 4. Add windowVals_length Lemma

```lean
lemma windowVals_length {L : Nat} (p : PathLen L) :
  (windowVals p).length = L := by
    simp [windowVals, p.len_eq]
```

**Verification:**
```lean
#check windowVals_length
-- Should compile and type-check
```

### 5. Add Window Sum Equality

This connects edge weights to the DP bound:

```lean
lemma windowVals_sum_eq_weightSum {L : Nat} (p : PathLen L) :
  (windowVals p).sum = weightSum p := by
    simp [windowVals, List.sum_map, weightSum]
```

---

## Success Criteria for Tier 2b

✅ Lemma8_DensityFloor.lean compiles without duplicate errors  
✅ `#check windowVals` passes  
✅ `#check windowVals_length` passes  
✅ No axioms in windowVals  
✅ `lake build` succeeds  

---

## Tier 2c Roadmap (After 2b Complete)

### Goal: Prove Path Lifting Theorem

This is the **CRITICAL LEMMA (B)** connecting arithmetic to graph:

```lean
lemma path_lifting (odd_steps : List (ℕ × ℕ)) :
  (∃ path : PathLen odd_steps.length,
    path.start ∈ reachable ∧
    ∀ i, (windowVals path).get i = (odd_steps.get i).val) ↔
  -- Equivalence to arithmetic odd-block sequence property
  sorry
```

**Will use:**
- `pathValidFrom_head` — first edge extraction
- `pathValidFrom_tail` — path induction
- `pathValidFrom_head_mem` — membership in edges
- `windowVals` and `windowVals_length` from Tier 2b

---

## Tier 3 Roadmap (After 2c Complete)

### Goal: Prove DP Coverage

This is the **CRITICAL LEMMA (C)** proving all reachable paths are bounded:

```lean
lemma dp_coverage (p : PathLen 16) :
  reachable p.start → weightSum p ≥ 29
```

**Strategy Decision Needed:**
- **Option A (Recommended):** DP inside Lean using min-plus matrix multiplication
- **Option B:** External DP certificate validated in Lean
- **❌ NOT Option C:** Brute-force enumeration (64^16 ≈ 2.3×10^28, infeasible)

---

## File Changes Summary

| File | Action | Status |
|------|--------|--------|
| Graph.lean | MOD, StateOK, isStart, mkState fixes | ✅ DONE |
| Path.lean | e ∈ edges + 3 lemmas | ✅ DONE |
| Lemma8_DensityFloor.lean | Delete OLD PathLen + window_of_path, add import | ⏳ TODO |
| Lemma8_DensityFloor.lean | Add windowVals + lemmas | ⏳ TODO (Tier 2b) |

---

## Documentation References

**For Current Status:**
- Read: [README_CRITICAL_FIXES.md](README_CRITICAL_FIXES.md) (this explains why fixes matter)
- Reference: [FIXES_COMPLETE_SUMMARY.md](FIXES_COMPLETE_SUMMARY.md) (quick summary)
- Details: [CRITICAL_FIXES_APPLIED.md](CRITICAL_FIXES_APPLIED.md) (full explanation)

**For Verification:**
- [VERIFICATION_ROADMAP.md](VERIFICATION_ROADMAP.md) (how to verify each fix)
- [EXACT_CODE_CHANGES.md](EXACT_CODE_CHANGES.md) (line-by-line changes)

**For Architecture:**
- [FINAL_CODE_STATE.md](FINAL_CODE_STATE.md) (complete file listings)

---

## Priority Order

### 🔴 URGENT (Do Today)
1. Fix git issue and verify `lake build` passes
2. Clean Lemma8_DensityFloor.lean (delete old definitions)
3. Verify no duplicate definition errors

### 🟡 HIGH (Do Next Session)
1. Implement Tier 2b (windowVals + lemmas)
2. Verify Tier 2b compiles
3. Run #check suite

### 🟢 MEDIUM (Do Later)
1. Implement Tier 2c (path_lifting proof)
2. Implement Tier 3 (dp_coverage proof)
3. Run final kernel verification

---

## Questions to Answer Before Tier 3

1. **DP Strategy:** Will you implement DP inside Lean or validate external certificate?
2. **Bound Value:** Is 29 the correct minimum weight bound? (Verify against basin analysis)
3. **Path Length:** Should paths be bounded at length 16, or is there flexibility?

---

## Success Metrics

| Milestone | Metric | Status |
|-----------|--------|--------|
| Tier 2a | 0 axioms, 0 sorries, all fixes applied | ✅ DONE |
| Tier 2b | windowVals, lemmas, lake build passes | ⏳ READY |
| Tier 2c | path_lifting compiles, no sorries | ⏳ READY |
| Tier 3 | dp_coverage compiles, no axioms | ⏳ READY |
| **FINAL** | **Zero axioms in proof kernel** | ⏳ GOAL |

---

## Time Estimate

- Git fix + cleanup: **30 minutes**
- Tier 2b: **1-2 hours**
- Tier 2c: **2-3 hours**
- Tier 3: **3-4 hours**
- **Total remaining: 6-10 hours**

---

## Next Session Agenda

1. ✅ Git network issue resolved
2. ✅ Lemma8_DensityFloor.lean cleaned
3. ⏳ Tier 2b implemented and verified
4. ⏳ Tier 2c strategy review
5. ⏳ Begin Tier 2c implementation

---

## Final Checklist Before Moving On

- [ ] `lake build` succeeds (git fixed)
- [ ] No errors in Lemma8_DensityFloor.lean
- [ ] OLD PathLen deleted
- [ ] OLD window_of_path deleted
- [ ] NEW import added to Lemma8_DensityFloor.lean
- [ ] Path.lean verified with #check suite
- [ ] Graph.lean verified with #check suite
- [ ] Understanding confirmed: Why each fix was critical

Once this checklist is complete, Tier 2b can be implemented with confidence.
