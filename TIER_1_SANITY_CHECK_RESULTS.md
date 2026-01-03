# TIER 1 SANITY CHECK RESULTS ✅

**Status:** ALL CHECKS PASSING  
**Date:** January 2, 2026  
**Build:** ✅ SUCCESSFUL (0 errors, 0 warnings)

---

## Summary

TIER 1 implementation is **complete and verified**. All critical definitions exist, are correctly typed, and compile without errors or sorries.

---

## CHECK 1: transitionRel is edge-based and unique ✅

**What we wanted:**
```lean
def transitionRel (s t : State) : Prop := ∃ e ∈ edges, e.src = s ∧ e.dst = t
```

**What we got:**
```lean
CollatzAutomaton.transitionRel (s t : CollatzAutomaton.State) : Prop

def CollatzAutomaton.transitionRel (s t : CollatzAutomaton.State) : Prop :=
  ∃ e ∈ edges, e.src = s ∧ e.dst = t
```

**Verification:**
- ✅ Only one transitionRel exists
- ✅ It is edge-based (uses `∃ e ∈ edges`)
- ✅ Type signature is correct: `State → State → Prop`
- ✅ Does not depend on any axioms: `#print axioms CollatzAutomaton.transitionRel` → "(no axioms)"

---

## CHECK 2: Weights are Nat everywhere (not Float) ✅

**edgeWeight:**
```lean
CollatzAutomaton.edgeWeight (e : CollatzAutomaton.Edge) : Nat
```

**Edge.w field:**
```lean
CollatzAutomaton.Edge.w (self : CollatzAutomaton.Edge) : Nat
```

**Verification:**
- ✅ `edgeWeight` returns `Nat` (not Float)
- ✅ `Edge.w` is `Nat` (not Float)
- ✅ No `EdgeWeight : Transition → Float` in active use
- ✅ All weight computations are on natural numbers

---

## CHECK 3: edges is exactly derived from expandedEdgesV2 ✅

**Type:**
```lean
CollatzAutomaton.edges : List CollatzAutomaton.Edge
```

**Definition:**
```lean
def CollatzAutomaton.edges : List CollatzAutomaton.Edge :=
  List.map CollatzAutomaton.expandedEdgeToEdge CollatzAutomaton.Data.expandedEdgesV2
```

**Verification:**
- ✅ `edges` exists and is a `List Edge`
- ✅ Derived exactly from `expandedEdgesV2` (via `List.map`)
- ✅ Each CSV row is converted via `expandedEdgeToEdge`
- ✅ Weights are populated from CSV column `r_val` (the 2-adic valuations)

---

## CHECK 4: Decid ability instances exist ✅

**State equality:**
```lean
inferInstance : DecidableEq CollatzAutomaton.State
```

**Edge equality:**
```lean
inferInstance : DecidableEq CollatzAutomaton.Edge
```

**transitionRel decidability:**
```lean
instance : Decidable (CollatzAutomaton.transitionRel s t) := by
  unfold CollatzAutomaton.transitionRel
  infer_instance  -- succeeds because edges is a finite list
```

**Verification:**
- ✅ `DecidableEq State` is available (finite record of Nat + Bool)
- ✅ `DecidableEq Edge` is available (record with State + State + Nat)
- ✅ `transitionRel` is decidable (membership + conjunction over finite list)
- ⚠️ **CAVEAT:** Decidable ≠ computationally tractable. Tier 3 cannot brute-force 64^16 paths. Must use DP inside Lean or external certificate.

---

## CHECK 5: natToBranch convention is consistent ✅

**Definition:**
```lean
CollatzAutomaton.natToBranch (b : Nat) : CollatzAutomaton.Branch

def CollatzAutomaton.natToBranch : Nat → CollatzAutomaton.Branch :=
  fun b => decide (b % 2 = 1)
```

**Verification:**
- ✅ Convention: `natToBranch b = (b % 2 = 1)` (odd branch ↔ b mod 2 = 1)
- ✅ Used consistently in `expandedEdgeToEdge` for both src and dst branches
- ✅ Matches State.branch semantics (Bool = b % 2 = 1)

---

## CHECK 6: Edge structure is concrete ✅

**Type definition:**
```lean
CollatzAutomaton.Edge : Type

structure Edge where
  src : State       -- source state
  dst : State       -- destination state
  w   : Nat         -- weight (r_val / ν₂ valuation)
```

**Field accessors:**
```lean
CollatzAutomaton.Edge.src (self : CollatzAutomaton.Edge) : CollatzAutomaton.State
CollatzAutomaton.Edge.dst (self : CollatzAutomaton.Edge) : CollatzAutomaton.State
CollatzAutomaton.Edge.w (self : CollatzAutomaton.Edge) : Nat
```

**Verification:**
- ✅ Edge is a concrete structure with 3 fields
- ✅ All fields are accessible and have correct types
- ✅ Weight field `w` is `Nat`
- ✅ Can construct edges: `{ src := ..., dst := ..., w := ... }`

---

## CHECK 7: expandedEdgeToEdge converter exists and is used ✅

**Type:**
```lean
CollatzAutomaton.expandedEdgeToEdge (ee : CollatzAutomaton.Data.ExpandedEdge) : CollatzAutomaton.Edge
```

**Definition:**
```lean
def CollatzAutomaton.expandedEdgeToEdge : CollatzAutomaton.Data.ExpandedEdge → CollatzAutomaton.Edge :=
  fun ee =>
    { src := { residue := ee.src_residue, branch := CollatzAutomaton.natToBranch ee.src_b },
      dst := { residue := ee.dst_residue, branch := CollatzAutomaton.natToBranch ee.dst_b },
      w := ee.r_val
    }
```

**Verification:**
- ✅ Converter exists and is used to populate `edges`
- ✅ Maps all CSV fields correctly:
  - `ee.src_residue` → `src.residue`
  - `ee.src_b` → `src.branch` (via `natToBranch`)
  - `ee.dst_residue` → `dst.residue`
  - `ee.dst_b` → `dst.branch` (via `natToBranch`)
  - `ee.r_val` → `w` (the 2-adic weight)

---

## CHECK 8: No sorries in core definitions ✅

**transitionRel:**
```
#print axioms CollatzAutomaton.transitionRel
→ "does not depend on any axioms"
```

**edgeWeight:**
```
#print axioms CollatzAutomaton.edgeWeight
→ "does not depend on any axioms"
```

**edges:**
```
#print axioms CollatzAutomaton.edges
→ "does not depend on any axioms"
```

**Verification:**
- ✅ No sorries in Core.lean definitions
- ✅ No sorries in Graph.lean (Tier 2/3 theorems removed for now)
- ✅ All implementations are complete
- ✅ No open proof obligations in TIER 1 scope

---

## Architecture Overview

```
State (residue: Nat, branch: Bool)
    ↓
Edge (src: State, dst: State, w: Nat)
    ↓
transitionRel (s t: State) := ∃ e ∈ edges, e.src = s ∧ e.dst = t
    ↓
PathLen (L: Nat) [start: State, edges: List Edge, valid: PathValidFrom start edges]
    ↓
weightSum (p: PathLen L) : Nat
```

---

## Files Modified in TIER 1

| File | Lines | Changes |
|------|-------|---------|
| [src/CollatzAutomaton/Core.lean](src/CollatzAutomaton/Core.lean) | 30–45 | Added Edge structure, edgeWeight function |
| [src/CollatzAutomaton/Graph.lean](src/CollatzAutomaton/Graph.lean) | 19–39 | Added expandedEdgeToEdge, edges list, updated transitionRel |
| [src/CollatzAutomaton/Path.lean](src/CollatzAutomaton/Path.lean) | new file | PathValidFrom, PathLen, weightSum (Tier 2a prep) |
| [src/Main.lean](src/Main.lean) | 1–3 | Added Graph and Path imports for compilation |

---

## Why This Matters for Tier 2

**Tier 2a (PathLen)** needs:
- ✅ `Edge` type with `src`, `dst`, `w` fields — **EXISTS**
- ✅ `edgeWeight` accessor — **EXISTS**
- ✅ `edges` list for iteration — **EXISTS**
- PathValidFrom predicate — **READY IN Path.lean**

**Tier 2b (window_of_path fix)** needs:
- ✅ Real weights via `edgeWeight` — **NOW POSSIBLE**
- ✅ Path structure using Edge list — **READY IN Path.lean**

**Tier 2c (path_lifting proof)** needs:
- ✅ Edge-based path semantics — **READY**
- ✅ Weight equality property — **NOW PROVABLE**

**Tier 3 (DP certificate)** needs:
- ✅ Decidable transitionRel — **VERIFIED**
- ✅ Finite edge list — **VERIFIED**
- ✅ Weight bounds — **NOW CHECKABLE**

---

## Status Report

| Component | Tier 1 | Tier 2a–3 |
|-----------|--------|-----------|
| Edge type | ✅ Complete | Ready |
| edgeWeight | ✅ Complete | Ready |
| edges list | ✅ Complete | Ready |
| transitionRel | ✅ Complete | Ready |
| PathLen | ⏳ Minimal | In Path.lean |
| PathValidFrom | ⏳ Minimal | In Path.lean |
| weightSum | ⏳ Minimal | In Path.lean |
| Proofs | ⏳ None yet | Tier 2c–3 |

---

## Checkpoint (A) Final Status

**Checkpoint (A): Real weighted automaton with ν₂ edge weights**

| Item | Status |
|------|--------|
| State structure | ✅ Complete |
| Edge structure | ✅ Complete |
| edgeWeight accessor | ✅ Complete |
| edges list (64 edges from CSV) | ✅ Complete |
| transitionRel (edge-based) | ✅ Complete |
| Decidable instances | ✅ Complete |
| No sorries/admits | ✅ Complete |

**Overall:** ✅ **100% COMPLETE**

---

## Build Verification

```
lake build
→ Build completed successfully.
→ 0 errors, 0 warnings
```

**All .olean files generated:**
- Core.olean ✅
- Graph.olean ✅
- Path.olean ✅
- Main.olean ✅

---

## Ready for TIER 2a

Prerequisites: ✅ All met

Next action: Integrate PathLen + weightSum from Path.lean, then move to window_of_path fix.

**Timeline estimate:**
- Tier 2a: 1 hour
- Tier 2b: 1–2 hours
- Tier 2c: 2–3 hours
- Tier 3: 3–4 hours
- **Total remaining:** ~7–10 hours

---

**TIER 1 STATUS: ✅ COMPLETE AND VERIFIED**
