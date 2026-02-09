# TIER 2b Cleanup Complete ✅

**Status:** All old path layer definitions removed; canonical Path.lean imported  
**Date:** January 2, 2026  
**Impact:** Eliminates residue % 10 bug, enables correct DP proof in Tier 3

## What Was Deleted

### From Lemma8_DensityFloor.lean

#### 1. OLD PathLen Structure (DELETED)
```lean
-- GONE:
structure PathLen (L : Nat) where
  start : State
  steps : List State
  len_eq : steps.length = L
```

**Why:** Used List State instead of List Edge, preventing proper edge-based reasoning

**Replaced with:** Import `CollatzAutomaton.Path` which provides:
```lean
structure PathLen (L : Nat) where
  start : State
  edges : List Edge        -- CORRECT: actual graph edges
  len_eq : edges.length = L
  valid : PathValidFrom start edges
```

---

#### 2. OLD window_of_path (DELETED)
```lean
-- GONE (THE FATAL BUG):
def window_of_path (p : PathLen L) : Window := by
  have h_vals : (List.range L).map (fun i =>
    if h : i < p.steps.length then (p.steps.get ⟨i, h⟩).residue % 10 else 0
  ).length = L := by simp [List.length_range]
  exact {
    vals := (List.range L).map (fun i =>
      if h : i < p.steps.length then (p.steps.get ⟨i, h⟩).residue % 10 else 0
    )
    len_eq := h_vals
  }
```

**Why:** 
- Uses `residue % 10` (arbitrary, incorrect)
- Works with List State (not edges)
- No connection to actual 2-adic valuations
- **BREAKS Tier 3:** DP proof would be about fake valuations

**Replaced with:** NEW windowVals in Path.lean:
```lean
def windowVals {L : Nat} (p : PathLen L) : List Nat :=
  p.edges.map edgeWeight

lemma windowVals_length {L : Nat} (p : PathLen L) :
  (windowVals p).length = L := by
  simp [windowVals, p.len_eq]
```

**Effect:**
- Uses `edgeWeight` (correct 2-adic valuation from edge structure)
- Works with List Edge (actual graph edges)
- Guaranteed edge membership via PathValidFrom constraint
- ✅ **ENABLES Tier 3:** DP proof covers real automaton

---

#### 3. OLD ReachableWindow (UPDATED)
```lean
-- WAS:
def ReachableWindow (w : Window) : Prop :=
  ∃ (p : PathLen L), reachable p.start ∧ window_of_path p = w

-- NOW:
def ReachableWindow (w : Window) : Prop :=
  ∃ (p : PathLen L), reachable p.start ∧ (windowVals p) = w.vals
```

**Effect:** ReachableWindow now references correct path definitions

---

#### 4. OLD Lemmas (UPDATED)
```lean
-- UPDATED:
lemma window_of_path_valid (p : PathLen L) :
  (window_of_path p).vals.length = L := by
  exact (window_of_path p).len_eq

-- NOW:
lemma windowVals_valid {L : Nat} (p : PathLen L) :
  (windowVals p).length = L := by
  exact windowVals_length p

-- UPDATED:
lemma reachable_path_yields_reachable_window (p : PathLen L) (h : reachable p.start) :
  ReachableWindow (window_of_path p) := by
  exact ⟨p, h, rfl⟩

-- NOW:
lemma reachable_path_yields_reachable_window {L : Nat} (p : PathLen L) (h : reachable p.start) :
  ReachableWindow { vals := windowVals p, len_eq := windowVals_length p } := by
  exact ⟨p, h, rfl⟩
```

---

## What Was Added

### To Path.lean
```lean
/-- Extract the 2-adic valuation window from a path.
    Maps each edge weight to a valuation value. -/
def windowVals {L : Nat} (p : PathLen L) : List Nat :=
  p.edges.map edgeWeight

/-- Lemma: window valuation list has correct length. -/
lemma windowVals_length {L : Nat} (p : PathLen L) :
  (windowVals p).length = L := by
  simp [windowVals, p.len_eq]

/-- The sum of window valuations equals the total path weight. -/
def windowSum {L : Nat} (p : PathLen L) : Nat :=
  weightSum p
```

### To Lemma8_DensityFloor.lean (top)
```lean
import CollatzAutomaton.Path
```

---

## Verification Results

### ✅ No Shadowing (Critical Audit Passed)

```bash
rg -n "structure PathLen" src/CollatzAutomaton
# Result: 1 match (Path.lean line 14 only)

rg -n "def PathValidFrom" src/CollatzAutomaton
# Result: 1 match (Path.lean line 8 only)

rg -n "def weightSum" src/CollatzAutomaton
# Result: 1 match (Path.lean line 21 only)
```

### ✅ No residue % 10 anywhere in proof-critical code

```bash
rg "residue.*%.*10" src/CollatzAutomaton
# Result: 0 matches in Path.lean, Lemma8_DensityFloor.lean, or Graph.lean
```

### ✅ PathValidFrom has edge membership constraint

[Path.lean](src/CollatzAutomaton/Path.lean#L8-L11):
```lean
def PathValidFrom (start : State) : List Edge → Prop
  | [] => True
  | e :: es =>
      e ∈ edges ∧ e.src = start ∧ PathValidFrom e.dst es
```

### ✅ isStart is finite

[Graph.lean](src/CollatzAutomaton/Graph.lean#L19-L43):
```lean
def MOD : Nat := 64
def StateOK (s : State) : Prop := s.residue < MOD

def isStart (s : State) : Prop :=
  s.branch = false ∧ s.residue % 2 = 1 ∧ StateOK s
```

---

## Dependency Chain (Verified)

```
Path.lean
  ├─ imports: Core.lean, Graph.lean
  └─ exports: PathLen, PathValidFrom, weightSum, windowVals, windowSum
  
Lemma8_DensityFloor.lean
  ├─ imports: Core, Graph, Path, DPMinWindowsV2, Lemma7
  └─ uses: PathLen, PathValidFrom, weightSum, windowVals, ReachableWindow
```

**No cycles. Clean imports.**

---

## Impact on Tiers

### Tier 2a (Just Completed)
✅ **Graph fixes applied:**
- MOD + StateOK for finite start set
- PathValidFrom includes e ∈ edges constraint
- mkState uses natToBranch consistently

✅ **Path module created with:**
- Canonical PathLen using List Edge
- PathValidFrom with membership check
- weightSum using foldl
- Helper lemmas for induction

### Tier 2b (Just Completed - Cleanup)
✅ **Lemma8 cleanup finished:**
- Old PathLen deleted (was broken)
- Old window_of_path deleted (had residue % 10 bug)
- windowVals added (correct edge weights)
- Import Path to use canonical definitions
- No shadowing, no axioms

### Tier 2c (Next - Path Lifting)
⏳ **Ready to prove:**
- Path lifting connects arithmetic to graph
- Uses pathValidFrom_head, head_src, tail_valid lemmas
- Will prove: odd-block sequence ↔ valid PathLen

### Tier 3 (Final - DP Coverage)
⏳ **Can now safely prove:**
- All reachable 16-step paths have weightSum ≥ 29
- Uses correct Path definitions (not fake residue % 10 values)
- DP certificate will be on real automaton, not phantom

---

## Critical Fixes Summary

| Fix | Before | After | Impact |
|-----|--------|-------|--------|
| PathLen structure | `steps : List State` | `edges : List Edge` | Proper graph paths |
| window_of_path | `residue % 10` hack | `edges.map edgeWeight` | Correct valuations |
| PathValidFrom | No edge check | `e ∈ edges ∧ ...` | Guaranteed graph membership |
| isStart | Infinite states | MOD-bounded | Finite reachable set |

---

## What This Enables

**Before cleanup:**
- DP proof would range over fake paths (residue % 10)
- Window sums not connected to edge weights
- isStart infinite; reachability meaningless
- Tier 3 DP certificate would be worthless

**After cleanup:**
- ✅ DP proof ranges over real graph edges
- ✅ Window sums = sum of 2-adic valuations
- ✅ isStart finite; reachability meaningful
- ✅ Tier 3 DP certificate proves real bound on automaton

---

## Verification Suite Location

**Run:** [TIER_2b_CLEANUP_VERIFICATION.lean](TIER_2b_CLEANUP_VERIFICATION.lean)

Checks:
- ✅ All canonical definitions present
- ✅ No axioms in critical functions
- ✅ windowVals uses proper edge weights
- ✅ PathValidFrom requires e ∈ edges
- ✅ isStart is finite (MOD constraint)
- ✅ No residue % 10 bugs
- ✅ Ready for Tier 2c

---

## Files Modified

| File | Changes | Status |
|------|---------|--------|
| Path.lean | Added windowVals, windowVals_length, windowSum | ✅ |
| Lemma8_DensityFloor.lean | Added Path import, updated ReachableWindow | ✅ |
| Lemma8_DensityFloor.lean | Deleted old PathLen structure | ✅ |
| Lemma8_DensityFloor.lean | Deleted broken window_of_path | ✅ |
| Lemma8_DensityFloor.lean | Updated related lemmas | ✅ |

---

## Next: Tier 2c

Implement path_lifting theorem:
```lean
lemma path_lifting {L : Nat} (p : PathLen L) :
  (∃ odd_steps : List (ℕ × ℕ),
    odd_steps.length = L ∧
    -- arithmetic properties --
  ) ↔
  (reachable p.start ∧ PathValidFrom p.start p.edges)
```

Will use:
- `PathValidFrom.head_mem` — edge membership
- `PathValidFrom.head_src` — source matching
- `PathValidFrom.tail_valid` — induction
- `windowVals` — valuation extraction

---

## Success Criteria

✅ `structure PathLen` appears 1× (Path.lean only)  
✅ `def PathValidFrom` appears 1× (Path.lean only)  
✅ `def weightSum` appears 1× (Path.lean only)  
✅ No `residue % 10` in proof code  
✅ `e ∈ edges` in PathValidFrom  
✅ isStart finite (MOD constraint)  
✅ No axioms in Path.lean  
✅ windowVals uses edgeWeight  
✅ Ready for Tier 2c

**ALL CRITERIA MET ✅**
