# Exact Code Changes Applied

## Graph.lean Changes

### Addition 1: MOD constant (NEW, lines 19-20)
```lean
/-- Modulus for residue universe: restricts States to finite set. -/
def MOD : Nat := 64
```

### Addition 2: StateOK predicate (NEW, lines 21-22)
```lean
/-- Predicate: a State is "ok" if its residue is in [0, MOD). -/
def StateOK (s : State) : Prop := s.residue < MOD
```

### Change 3: Updated isStart definition (MODIFIED, lines 41-45)
**OLD:**
```lean
def isStart (s : State) : Prop :=
  s.branch = false ∧ s.residue % 2 = 1
```

**NEW:**
```lean
def isStart (s : State) : Prop :=
  s.branch = false ∧ s.residue % 2 = 1 ∧ StateOK s
```
**Key change:** Added `∧ StateOK s` to constrain to finite universe

### Change 4: Updated mkState definition (MODIFIED, lines 55-57)
**OLD:**
```lean
def mkState (r : Nat) (b : Nat) : State :=
  { residue := r, branch := (b = 1) }
```

**NEW:**
```lean
def mkState (r : Nat) (b : Nat) : State :=
  { residue := r, branch := natToBranch b }
```
**Key change:** Use `natToBranch b` instead of `(b = 1)` for consistency

---

## Path.lean Complete Replacement

### File: src/CollatzAutomaton/Path.lean (REWRITTEN)

**Lines 1-2:** Imports (unchanged from previous)
```lean
import CollatzAutomaton.Core
import CollatzAutomaton.Graph
```

**Lines 4-5:** Namespace
```lean
namespace CollatzAutomaton
```

**Lines 7-11: Updated PathValidFrom (MODIFIED)**
**OLD:**
```lean
def PathValidFrom (start : State) : List Edge → Prop
  | [] => True
  | e :: es => e.src = start ∧ PathValidFrom e.dst es
```

**NEW:**
```lean
/-- A path is valid if each edge is in the global edge list,
    and edges chain correctly from the given start state. -/
def PathValidFrom (start : State) : List Edge → Prop
  | [] => True
  | e :: es =>
      e ∈ edges ∧ e.src = start ∧ PathValidFrom e.dst es
```
**Key change:** Added `e ∈ edges ∧` before the source check

**Lines 13-18:** PathLen structure (unchanged except doc)
```lean
/-- A path of exactly L edges with proof that it's valid. -/
structure PathLen (L : Nat) where
  start : State
  edges : List Edge
  len_eq : edges.length = L
  valid : PathValidFrom start edges
```

**Lines 20-22:** weightSum definition (same as before)
```lean
/-- Sum the weights of all edges in a path. -/
def weightSum {L : Nat} (p : PathLen L) : Nat :=
  p.edges.foldl (fun acc e => acc + edgeWeight e) 0
```

**Lines 24-26: NEW PathValidFrom.head_mem lemma**
```lean
lemma PathValidFrom.head_mem {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → e ∈ edges := by
  intro h; exact h.1
```

**Lines 28-30: NEW PathValidFrom.head_src lemma**
```lean
lemma PathValidFrom.head_src {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → e.src = start := by
  intro h; exact h.2.1
```

**Lines 32-34: NEW PathValidFrom.tail_valid lemma**
```lean
lemma PathValidFrom.tail_valid {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → PathValidFrom e.dst es := by
  intro h; exact h.2.2
```

**Line 36:** Closing namespace
```lean
end CollatzAutomaton
```

---

## Summary of Changes by Type

### Added (3 items in Graph.lean)
1. `def MOD : Nat := 64`
2. `def StateOK (s : State) : Prop := s.residue < MOD`
3. `∧ StateOK s` constraint in isStart

### Modified (2 items)
1. Graph.lean `isStart`: Added StateOK constraint
2. Graph.lean `mkState`: Changed from `(b = 1)` to `natToBranch b`
3. Path.lean `PathValidFrom`: Added `e ∈ edges ∧` requirement

### Added (3 lemmas in Path.lean)
1. `lemma PathValidFrom.head_mem`
2. `lemma PathValidFrom.head_src`
3. `lemma PathValidFrom.tail_valid`

---

## Verification: Exact Line Numbers

| File | Lines | Change | Type |
|------|-------|--------|------|
| Graph.lean | 19-20 | Add MOD | NEW |
| Graph.lean | 21-22 | Add StateOK | NEW |
| Graph.lean | 41-45 | Update isStart | MODIFIED |
| Graph.lean | 55-57 | Update mkState | MODIFIED |
| Path.lean | 7-11 | Update PathValidFrom | MODIFIED |
| Path.lean | 24-26 | Add head_mem lemma | NEW |
| Path.lean | 28-30 | Add head_src lemma | NEW |
| Path.lean | 32-34 | Add tail_valid lemma | NEW |

---

## No Changes To

- Core.lean — Edge structure unchanged
- Main.lean — Imports unchanged
- ExpandedEdgesV2 — CSV data unchanged
- ReachableNodesV2 — Graph structure unchanged

---

## Result

✅ All three critical fixes applied  
✅ Code is syntactically valid  
✅ No axioms introduced  
✅ Clean dependency chain  
✅ Ready for Tier 2b after cleanup
