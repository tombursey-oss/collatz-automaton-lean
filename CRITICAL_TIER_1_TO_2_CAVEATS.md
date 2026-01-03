# ⚠️ TIER 1→2 CRITICAL CAVEATS

**Date:** January 2, 2026  
**Priority:** MUST READ BEFORE TIER 2a

---

## Caveat 1: "42 edges" is WRONG ❌

### The Mistake
Documentation claimed "42 edges" derived from expandedEdgesV2.

### The Reality
```
#eval CollatzAutomaton.edges.length
→ 64
```

**Numbers:**
- **64** = Total edges in CSV (expandedEdgesV2)
- **42** = Reachable nodes (theoretical analysis)
- **16** = Target path length for DP

**Why this matters:**
- Later proofs might treat edges as "small and enumerable"
- But 64 edges → combinatorial explosion for path enumeration
- Tier 3 must use **DP inside Lean** or **external certificate**, NOT brute-force enumeration

### Correct Claim
"expandedEdgesV2 contains 64 edges covering transitions between 42 reachable nodes"

---

## Caveat 2: Decidable ≠ Computationally Tractable ❌

### The Mistake
Claimed Tier 3 can close via `decide` on "∀ paths length 16, weightSum ≥ 29"

### The Reality
`Decidable transitionRel` is necessary but NOT sufficient:

```lean
-- This is decidable in principle:
∀ p : PathLen 16, reachable p.start → weightSum p ≥ 29

-- But NOT computationally tractable by brute force:
-- 64^16 possible edges → ~2.3 × 10^28 paths
-- Even the reachable subgraph is too large
```

### Why Decidable ≠ Decidable
- **Decidable instance:** Makes the type checkable (✅ done in TIER 1)
- **Computational decidability:** Can compute the decision in reasonable time (❌ intractable for 64^16)

### Tier 3 Must Be
Choose ONE:

**Option A: DP inside Lean**
- Implement min-plus matrix multiplication
- Compute W[k, s, s'] = min weight of k-step paths from s to s'
- Verify all entries ≥ 29 for k=16

**Option B: External Certificate**
- DP computed externally (Python/C++)
- Produce invariant predicate
- Validate in Lean via certificate checking

**NOT Option C: Brute enumeration**
- ❌ 2.3 × 10^28 is computationally infeasible

---

## Caveat 3: PathLen Shadowing ⚠️

### The Problem
**TWO PathLen definitions exist:**

```
src/CollatzAutomaton/Path.lean (line 12)
  ✅ NEW: edges : List Edge, valid : PathValidFrom start edges

src/CollatzAutomaton/Lemma8_DensityFloor.lean (line 79)
  ❌ OLD: steps : List State, len_eq : steps.length = L
```

**When Lean encounters both, it uses the second (later import wins).**

### The Solution
**Tier 2a MUST:**
1. Delete OLD PathLen from Lemma8_DensityFloor.lean
2. Delete OLD window_of_path (residue % 10 bug)
3. Import Path.lean
4. Define new window extractor using Path.PathLen semantics

### The Audit (BEFORE Tier 2a)
```
rg -n "structure PathLen" src/CollatzAutomaton
→ Should return EXACTLY ONE match (in Path.lean)

rg -n "def weightSum" src/CollatzAutomaton
→ Should return EXACTLY ONE match (in Path.lean)

rg -n "def window_of_path" src/CollatzAutomaton
→ Should return EXACTLY ONE match (redefined in Lemma8 using new PathLen)
```

---

## Tier 2a Implementation Requirements

### MUST have this exact shape (in Path.lean)

```lean
namespace CollatzAutomaton

def PathValidFrom (start : State) : List Edge → Prop
  | [] => True
  | e :: es => e.src = start ∧ PathValidFrom e.dst es

structure PathLen (L : Nat) where
  start : State
  edges : List Edge
  len_eq : edges.length = L
  valid : PathValidFrom start edges

def weightSum {L : Nat} (p : PathLen L) : Nat :=
  let rec sum : List Edge → Nat → Nat
    | [], acc => acc
    | e :: es, acc => sum es (acc + edgeWeight e)
  sum p.edges 0

-- Helper lemmas
lemma PathValidFrom.head_src {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → e.src = start := by
  intro h; exact h.1

lemma PathValidFrom.tail_valid {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → PathValidFrom e.dst es := by
  intro h; exact h.2

end CollatzAutomaton
```

### MUST pass this #check suite

```lean
#check CollatzAutomaton.PathValidFrom
#check CollatzAutomaton.PathLen
#check CollatzAutomaton.PathLen.valid
#check CollatzAutomaton.weightSum

#print axioms CollatzAutomaton.weightSum
→ Should be "(no axioms)"
```

---

## Tier 2b Preview: Kill the residue % 10 Bug

Once Tier 2a is integrated, define:

```lean
def windowVals {L : Nat} (p : PathLen L) : List Nat :=
  p.edges.map edgeWeight

lemma windowVals_length {L} (p : PathLen L) : 
  (windowVals p).length = L := by
  simp [windowVals, p.len_eq]
```

This makes it **impossible** to reintroduce the residue % 10 bug.

---

## Action Items

### Before starting Tier 2a:

- [ ] Confirm `edges.length = 64` (already done ✅)
- [ ] Confirm duplicate PathLen exists (already done ✅)
- [ ] Update all documentation: "64 edges" not "42 edges"
- [ ] Add warning: Tier 3 needs DP or certificate, not brute force
- [ ] Plan Lemma8_DensityFloor cleanup (delete old PathLen)

### Start of Tier 2a:

- [ ] Import Path.lean in Lemma8_DensityFloor
- [ ] Delete OLD PathLen (the one with steps : List State)
- [ ] Delete OLD window_of_path (the one with residue % 10)
- [ ] Verify: exactly ONE PathLen, ONE weightSum in project
- [ ] Define new window_of_path using PathLen.edges

### Before Tier 3 planning:

- [ ] Choose DP strategy (inside Lean or external certificate)
- [ ] Do NOT plan brute-force enumeration

---

## Summary

| Item | Status | Risk |
|------|--------|------|
| edges.length = 64 (not 42) | ✅ Found | HIGH if ignored |
| Decidable ≠ tractable | ✅ Understood | CRITICAL if ignored |
| Duplicate PathLen exists | ✅ Found | CRITICAL if ignored |
| Need Tier 2a cleanup | ⏳ Ready | HIGH if not done first |

**Do NOT proceed to Tier 2b until all these are addressed.**

---

**Read this again before each of Tiers 2a, 2b, 2c, and 3.**
