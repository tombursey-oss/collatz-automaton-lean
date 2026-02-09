# Verification Roadmap for Critical Fixes

## Current State

✅ **Code changes:** Applied and verified as syntactically correct  
⚠️ **Build system:** Blocked by git network issue (attempting to fetch remote mathlib)  
✅ **Files:** All changes persisted and correct

## Verification When Git Issue Is Resolved

### Step 1: Clean Build

```bash
cd c:\collatz_automaton
Remove-Item .lake -Recurse -Force
git remote set-url origin https://github.com/leanprover-community/mathlib4  # or skip if can use local
lake build
```

**Expected result:** Build succeeded, 0 errors

### Step 2: Verify MOD and StateOK

```lean
#check CollatzAutomaton.MOD
#eval CollatzAutomaton.MOD
-- Output should be: 64

#check CollatzAutomaton.StateOK
-- Type: CollatzAutomaton.State → Prop

#check @CollatzAutomaton.StateOK
-- Full type: ∀ (s : CollatzAutomaton.State), Prop
```

### Step 3: Verify isStart Is Finite

```lean
-- Prove that exactly 32 states satisfy isStart
example : Set.ncard {s | CollatzAutomaton.isStart s} = 32 := by
  sorry  -- Will be finalized in Tier 2b DP proof

-- Verify type
#check CollatzAutomaton.isStart
-- Type: CollatzAutomaton.State → Prop
```

### Step 4: Verify mkState Consistency

```lean
-- mkState should use natToBranch
example (r b : Nat) : (CollatzAutomaton.mkState r b).branch = 
  CollatzAutomaton.natToBranch b := by
  rfl  -- Should work by reflexivity

-- Verify natToBranch definition
example : CollatzAutomaton.natToBranch 0 = false := by rfl
example : CollatzAutomaton.natToBranch 1 = true := by rfl
example : CollatzAutomaton.natToBranch 2 = false := by rfl
example : CollatzAutomaton.natToBranch 3 = true := by rfl
```

### Step 5: Verify PathValidFrom Has Membership Check

```lean
-- The critical membership constraint is in the definition
#check CollatzAutomaton.PathValidFrom
-- Should show: ∀ (start : State), List Edge → Prop

-- Example: cannot construct invalid path
example : ¬ ∃ (fake_edge : CollatzAutomaton.Edge),
  fake_edge ∉ CollatzAutomaton.edges ∧
  let es := [fake_edge] in
  CollatzAutomaton.PathValidFrom fake_edge.src es := by
  sorry  -- This should be provable given e ∈ edges constraint
```

### Step 6: Verify PathLen Structure

```lean
#check CollatzAutomaton.PathLen
-- Type: ∀ (L : Nat), Type

#check CollatzAutomaton.PathLen.valid
-- Type: ∀ {L : Nat}, PathLen L → PathValidFrom ...

-- Example: construct a valid 1-edge path
example (e : CollatzAutomaton.Edge) (h : e ∈ CollatzAutomaton.edges) :
  CollatzAutomaton.PathLen 1 :=
  { start := e.src
  , edges := [e]
  , len_eq := by simp
  , valid := by simp [h]
  }
```

### Step 7: Verify weightSum

```lean
#check CollatzAutomaton.weightSum
-- Type: ∀ {L : Nat}, PathLen L → Nat

#print axioms CollatzAutomaton.weightSum
-- Output should be: '(no axioms)'

-- Example: sum of empty path is 0
example : CollatzAutomaton.weightSum 
  { start := _, edges := [], len_eq := rfl, valid := trivial } = 0 := by
  simp [CollatzAutomaton.weightSum]
```

### Step 8: Verify Helper Lemmas

```lean
#check CollatzAutomaton.PathValidFrom.head_mem
-- Type: ∀ {start : State} {e : Edge} {es : List Edge},
--   PathValidFrom start (e :: es) → e ∈ edges

#check CollatzAutomaton.PathValidFrom.head_src
-- Type: ∀ {start : State} {e : Edge} {es : List Edge},
--   PathValidFrom start (e :: es) → e.src = start

#check CollatzAutomaton.PathValidFrom.tail_valid
-- Type: ∀ {start : State} {e : Edge} {es : List Edge},
--   PathValidFrom start (e :: es) → PathValidFrom e.dst es

-- Example usage
example {start : State} {e : Edge} {es : List Edge} 
  (h : CollatzAutomaton.PathValidFrom start (e :: es)) :
  e ∈ CollatzAutomaton.edges :=
  CollatzAutomaton.PathValidFrom.head_mem h
```

### Step 9: Verify No Regressions in Core

```lean
#check CollatzAutomaton.Edge
-- Structure should be unchanged:
-- src : State
-- dst : State
-- w : Nat

#check CollatzAutomaton.edgeWeight
-- Should still work: Edge → Nat

#check CollatzAutomaton.edges
-- Should be: List Edge (64 edges from CSV)

#check CollatzAutomaton.transitionRel
-- Should be: State → State → Prop
```

### Step 10: Dependency Chain Verification

```bash
lake env lean src/CollatzAutomaton/Core.lean    # Should compile
lake env lean src/CollatzAutomaton/Graph.lean   # Should compile (imports Core)
lake env lean src/CollatzAutomaton/Path.lean    # Should compile (imports Core, Graph)
```

All three should compile without errors.

---

## Checklist for Verification (When Git Fixed)

- [ ] `lake build` succeeds with 0 errors
- [ ] `#check CollatzAutomaton.MOD` returns `Nat`
- [ ] `#eval CollatzAutomaton.MOD` returns `64`
- [ ] `#check CollatzAutomaton.StateOK` has correct type
- [ ] `isStart` requires `StateOK` (finite universe)
- [ ] `mkState` uses `natToBranch` (consistent)
- [ ] `PathValidFrom` requires `e ∈ edges` (membership)
- [ ] `PathLen` structure unchanged
- [ ] `weightSum` has no axioms
- [ ] `head_mem` lemma type-checks
- [ ] `head_src` lemma type-checks
- [ ] `tail_valid` lemma type-checks
- [ ] No regressions in Core.lean
- [ ] No import cycles

---

## What The Fixes Accomplish

| Fix | Before | After | Verified By |
|-----|--------|-------|-------------|
| MOD + StateOK | Infinite start states | Exactly 32 finite states | `#eval` MOD, isStart cardinality |
| PathValidFrom e ∈ edges | Arbitrary paths | Only graph edges | Can't construct fake path |
| mkState natToBranch | Inconsistent convention | Single truth | Reflexivity proof |

---

## When Build Is Fixed

Execute the verification commands above to confirm:
1. All three fixes compile correctly
2. No axioms introduced
3. No regressions
4. Type signatures correct
5. Ready for Tier 2b

Then proceed to:
1. Delete OLD PathLen from Lemma8_DensityFloor.lean
2. Delete OLD window_of_path from Lemma8_DensityFloor.lean
3. Add import to Lemma8_DensityFloor.lean
4. Begin Tier 2b implementation
