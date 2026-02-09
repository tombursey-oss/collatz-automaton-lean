# Current Codebase State (After Tier 2b Cleanup)

**Date:** January 2, 2026  
**Phase:** All Tier 2 prerequisites complete  
**Next:** Ready for Tier 2c (path_lifting proof)

---

## File Structure

```
src/CollatzAutomaton/
├── Core.lean                      ✅ STABLE
│   ├─ State structure
│   ├─ Edge structure (src, dst, w)
│   └─ edgeWeight accessor
│
├── Graph.lean                     ✅ COMPLETE (with fixes)
│   ├─ MOD := 64
│   ├─ StateOK : s.residue < MOD
│   ├─ natToBranch : Branch extraction
│   ├─ expandedEdgeToEdge : CSV → Edge
│   ├─ edges : List Edge (64 total)
│   ├─ transitionRel : State → State → Prop
│   ├─ isStart : finite (32 states)
│   ├─ mkState : uses natToBranch
│   └─ reachable : inductive closure
│
├── Path.lean                      ✅ NEW & CANONICAL
│   ├─ PathValidFrom : e ∈ edges ∧ chain
│   ├─ PathLen L : structure with edges
│   ├─ weightSum : edge weight sum
│   ├─ windowVals : edge weight list
│   ├─ windowSum : alias for weightSum
│   ├─ PathValidFrom.head_mem : lemma
│   ├─ PathValidFrom.head_src : lemma
│   ├─ PathValidFrom.tail_valid : lemma
│   └─ windowVals_length : lemma
│
├── Lemma8_DensityFloor.lean       ✅ UPDATED
│   ├─ import CollatzAutomaton.Path
│   ├─ Window : structure
│   ├─ valuation_sum : window sum
│   ├─ dpWindow0 : DP window
│   ├─ R_min := 29
│   ├─ ReachableWindow : uses windowVals
│   ├─ windowVals_valid : lemma
│   └─ reachable_path_yields_reachable_window : lemma
│
├── Main.lean                      ✅ STABLE
│   └─ Imports: Core, Path (for lib compilation)
│
└── Other files                    ✅ UNCHANGED
    └─ (Lemma7, Tests, Data files, etc.)
```

---

## Definition Uniqueness (Audit Results)

```
❌ OLD: structure PathLen in Lemma8_DensityFloor (with steps : List State) — DELETED
✅ NEW: structure PathLen in Path.lean (with edges : List Edge) — CANONICAL

❌ OLD: def window_of_path with residue % 10 — DELETED
✅ NEW: def windowVals in Path.lean using edgeWeight — CANONICAL

✅ PathValidFrom : Path.lean only (with e ∈ edges)
✅ weightSum : Path.lean only (using foldl)
✅ isStart : Graph.lean only (with MOD constraint)
✅ reachable : Graph.lean only
✅ edges : Graph.lean only
```

**Result: Perfect — no shadowing, one source of truth for each concept.**

---

## Critical Properties

### 1. Path Membership is Enforced

**In Path.lean:**
```lean
def PathValidFrom (start : State) : List Edge → Prop
  | [] => True
  | e :: es => e ∈ edges ∧ e.src = start ∧ PathValidFrom e.dst es
                 ^^^^^^^^ CRITICAL
```

**Effect:** Every edge in a path is guaranteed to be in the global `edges` list.

---

### 2. Start Set is Finite

**In Graph.lean:**
```lean
def MOD : Nat := 64
def StateOK (s : State) : Prop := s.residue < MOD

def isStart (s : State) : Prop :=
  s.branch = false ∧ s.residue % 2 = 1 ∧ StateOK s
  ^^^^^^^^^^^^^^^^ 32 maximum states (odd residues in [1,63])
```

**Effect:** Reachable set is finite and bounded.

---

### 3. Valuations are Correct

**In Path.lean:**
```lean
def windowVals {L : Nat} (p : PathLen L) : List Nat :=
  p.edges.map edgeWeight
  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Uses edge weight field (2-adic valuation), not fake residue % 10
```

**Effect:** DP proof will be about correct 2-adic valuations.

---

### 4. No Axioms in Path Infrastructure

**Verified:**
```
#print axioms CollatzAutomaton.PathValidFrom    → (no axioms)
#print axioms CollatzAutomaton.PathLen          → (no axioms)
#print axioms CollatzAutomaton.weightSum        → (no axioms)
#print axioms CollatzAutomaton.windowVals       → (no axioms)
```

---

## Ready-to-Use Building Blocks

### Path Construction
```lean
-- Build a path from edges
example (edges_list : List Edge) (h_valid : PathValidFrom start edges_list) :
  PathLen edges_list.length := by
  exact ⟨start, edges_list, rfl, h_valid⟩
```

### Path Properties
```lean
-- Extract weight sum
example {L : Nat} (p : PathLen L) : Nat := weightSum p

-- Extract valuations
example {L : Nat} (p : PathLen L) : List Nat := windowVals p

-- Prove length preservation
example {L : Nat} (p : PathLen L) : (windowVals p).length = L :=
  windowVals_length p
```

### Induction on Paths
```lean
-- Prove property for all valid paths
example {L : Nat} (p : PathLen L) :
  (∀ i, (p.edges.get i) ∈ edges) := by
  induction L with
  | zero => sorry
  | succ n ih =>
    have h : PathValidFrom p.start p.edges := p.valid
    have h_mem := PathValidFrom.head_mem h
    have h_tail := PathValidFrom.tail_valid h
    -- Use h_mem and ih on tail
    sorry
```

---

## What Tier 2c Will Prove

**Goal:** path_lifting theorem

```lean
lemma path_lifting {L : Nat} (p : PathLen L) :
  ( ∃ (odd_steps : List (ℕ × ℕ)),
    odd_steps.length = L ∧
    (∀ i h : i < L,
      let e := p.edges.get ⟨i, _⟩
      (odd_steps.get ⟨i, _⟩).1 = e.src.residue ∧
      (odd_steps.get ⟨i, _⟩).2 = e.src.branch
    )
  ) ↔
  (reachable p.start ∧ PathValidFrom p.start p.edges)
```

**Uses:**
- `PathValidFrom.head_mem` for edge membership
- `PathValidFrom.head_src` for source matching
- `PathValidFrom.tail_valid` for tail validity
- Induction on path length
- State property extraction

---

## What Tier 3 Will Prove

**Goal:** dp_coverage theorem

```lean
lemma dp_coverage (p : PathLen 16) :
  reachable p.start → weightSum p ≥ 29
```

**Uses:**
- `path_lifting` from Tier 2c
- DP certificate (external validity)
- `reachable` induction
- `weightSum` properties

---

## Compilation Status

```
✅ Core.lean                → compiles cleanly
✅ Graph.lean               → compiles cleanly
✅ Path.lean                → compiles cleanly
✅ Lemma8_DensityFloor.lean → compiles cleanly (imports Path)
✅ Main.lean                → compiles cleanly (for library)

→ NO AXIOMS in critical infrastructure
→ NO SORRIES in canonical definitions
→ NO CIRCULAR IMPORTS
→ NO SHADOWING DEFINITIONS
```

---

## Known States

### Reachable Set
- **Start set:** `isStart` matches 32 states (odd residues, branch 0)
- **All reachable:** Finite, computed via `reachable.start` + `reachable.step`
- **Bound:** All states have `residue < 64` (by MOD constraint)

### Path Space
- **Paths:** All use edges from global `edges` list (64 edges)
- **Validity:** Enforced by `PathValidFrom` requiring `e ∈ edges`
- **Length:** Tracked by `PathLen L` structure
- **Weights:** Extracted via `edgeWeight` from edges

### Window Properties
- **Valuation extraction:** `windowVals` maps edges to weights
- **Length preservation:** `windowVals_length` proves length invariant
- **Sum properties:** `weightSum` = `windowSum` = sum of `windowVals`

---

## Dependency Graph

```
Core
  ↓ (State, Edge)
Graph (public: edges, transitionRel, reachable, isStart, MOD, StateOK)
  ↓ (uses Edge, edges)
Path (public: PathLen, PathValidFrom, weightSum, windowVals + lemmas)
  ↓ (uses Graph definitions)
Lemma8_DensityFloor (public: Window, ReachableWindow, R_min)
  ↓ (uses Path + Graph)
Lemma2_PathLifting (TO IMPLEMENT)
  ↓ (proves path_lifting using Path lemmas)
Lemma3_DPCoverage (TO IMPLEMENT)
  ↓ (proves dp_coverage using path_lifting)
Main (kernel verification)
```

**Cycles:** None ✅

---

## Testing the Infrastructure

**Quick verification:**

```lean
-- All these should #check successfully:
#check CollatzAutomaton.PathLen
#check CollatzAutomaton.PathValidFrom
#check CollatzAutomaton.weightSum
#check CollatzAutomaton.windowVals
#check CollatzAutomaton.edges
#check CollatzAutomaton.reachable
#check CollatzAutomaton.isStart
#check CollatzAutomaton.MOD

-- All should show (no axioms):
#print axioms CollatzAutomaton.PathLen
#print axioms CollatzAutomaton.PathValidFrom
#print axioms CollatzAutomaton.weightSum

-- Audit should return exactly 1 match each:
rg "structure PathLen" src/CollatzAutomaton       -- 1 (Path.lean)
rg "def PathValidFrom" src/CollatzAutomaton       -- 1 (Path.lean)
rg "def weightSum" src/CollatzAutomaton           -- 1 (Path.lean)

-- Should find 0 matches:
rg "residue.*%.*10" src/CollatzAutomaton          -- 0
```

---

## Summary

**Tier 2b Status:** ✅ **100% COMPLETE**

- ✅ Old broken definitions deleted
- ✅ Canonical Path.lean created
- ✅ Lemma8 updated to use canonical
- ✅ No shadowing (verified)
- ✅ No residue % 10 (verified)
- ✅ e ∈ edges enforced (verified)
- ✅ isStart finite (verified)
- ✅ No axioms (verified)
- ✅ All helper lemmas in place
- ✅ Ready for Tier 2c

**What's ready:**
- Path infrastructure ✅
- Graph infrastructure ✅
- Window extraction ✅
- Helper lemmas ✅

**What's next:**
- Tier 2c: path_lifting proof (2-3 hours)
- Tier 3: dp_coverage proof (3-4 hours)
- Final: kernel verification ✅

---

**All systems go for Tier 2c! 🚀**
