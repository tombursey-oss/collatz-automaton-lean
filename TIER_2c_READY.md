# TIER 2c: Ready to Implement

**Status:** ✅ All prerequisites complete  
**Blockers:** None  
**Estimated Time:** 2-3 hours  
**Objective:** Prove path_lifting theorem (BRIDGE LEMMA B)

---

## What You're Proving

The **path_lifting theorem** connects arithmetic (odd-block sequences) to the graph (valid paths):

```lean
lemma path_lifting {L : Nat} (p : PathLen L) :
  ( ∃ (odd_steps : List (ℕ × ℕ)),
    odd_steps.length = L ∧
    (∀ i, (odd_steps.get i).1 = -- residue of step i --) ∧
    (∀ i, (odd_steps.get i).2 = -- branch of step i --)
  ) ↔
  (reachable p.start ∧ PathValidFrom p.start p.edges)
```

**Meaning:** A path is valid in the graph iff its sequence of states matches an arithmetic odd-block sequence.

---

## Tools You Have

### From Path.lean (ready to use)

```lean
-- Core definitions
PathLen L : Type
  fields: start : State, edges : List Edge, len_eq, valid

PathValidFrom : State → List Edge → Prop
  requires: e ∈ edges ∧ e.src = start ∧ PathValidFrom e.dst es

weightSum {L : Nat} (p : PathLen L) : Nat
  = p.edges.foldl (· + edgeWeight ·) 0

windowVals {L : Nat} (p : PathLen L) : List Nat
  = p.edges.map edgeWeight

-- Helper lemmas (induction workhorses)
PathValidFrom.head_mem : e ∈ edges
PathValidFrom.head_src : e.src = start
PathValidFrom.tail_valid : PathValidFrom e.dst es

-- Length lemmas
windowVals_length : (windowVals p).length = L
```

### From Graph.lean (ready to use)

```lean
-- Core definitions
edges : List Edge  -- 64 edges from CSV
transitionRel : State → State → Prop
reachable : State → Prop  -- finite set via MOD constraint

-- Edge access
edgeWeight : Edge → Nat

-- Start constraint
isStart : State → Prop
  requires: s.branch = false ∧ s.residue % 2 = 1 ∧ s.residue < MOD
MOD := 64
StateOK : s.residue < MOD
```

---

## Proof Strategy (Outline)

### Direction 1: Graph → Arithmetic
```lean
lemma path_to_arithmetic {L : Nat} (p : PathLen L) :
  reachable p.start ∧ PathValidFrom p.start p.edges →
  ∃ odd_steps : List (ℕ × ℕ), 
    odd_steps.length = L ∧
    (∀ i, (odd_steps.get i).1 = (p.edges.get i).src.residue) ∧
    (∀ i, (odd_steps.get i).2 = (p.edges.get i).src.branch)
```

**Proof idea:**
1. Use `p.valid : PathValidFrom p.start p.edges`
2. For each edge in `p.edges`, extract the source state
3. Map each state to (residue, branch) pair
4. Result is the arithmetic sequence

**Lemmas to use:**
- `windowVals_length` for length preservation
- `PathValidFrom.head_src` for source extraction
- Induction on `p.edges` length

### Direction 2: Arithmetic → Graph
```lean
lemma arithmetic_to_path {L : Nat} (odd_steps : List (ℕ × ℕ)) :
  odd_steps.length = L ∧
  (-- arithmetic properties --) →
  ∃ p : PathLen L,
    reachable p.start ∧ PathValidFrom p.start p.edges
```

**Proof idea:**
1. Use `odd_steps` to construct a list of edges
2. Prove each edge is in `edges` via DP coverage
3. Prove path validity via `PathValidFrom` construction
4. Prove start is reachable via `isStart` and `reachable` induction

**Lemmas to use:**
- `PathValidFrom.head_mem` to prove edge membership
- `transitionRel` lemmas for reachability
- `reachable.step` constructor

---

## Implementation Sketch

```lean
namespace CollatzAutomaton

-- Bridge Lemma: Path Lifting (connects arithmetic to graph)
lemma path_lifting {L : Nat} (p : PathLen L) :
  ( ∃ (odd_steps : List (ℕ × ℕ)),
    odd_steps.length = L ∧
    (∀ i h : i < L,
      let e := p.edges.get ⟨i, by simp [p.len_eq]; exact h⟩
      (odd_steps.get ⟨i, by simp; exact h⟩).1 = e.src.residue ∧
      (odd_steps.get ⟨i, by simp; exact h⟩).2 = e.src.branch
    )
  ) ↔
  (reachable p.start ∧ PathValidFrom p.start p.edges) := by
  constructor
  · -- arithmetic_to_path: given odd_steps, construct valid path
    intro ⟨odd_steps, len_eq, props⟩
    -- Use props to build p.edges and prove properties
    sorry
  · -- path_to_arithmetic: given valid path, extract odd_steps
    intro ⟨h_reach, h_valid⟩
    -- Use h_valid to extract states from edges
    sorry

end CollatzAutomaton
```

---

## Verification Checklist

Before submitting Tier 2c:

- [ ] `#check path_lifting` compiles
- [ ] `#print axioms path_lifting` shows no axioms
- [ ] Can induct on `p.edges` length
- [ ] Can extract `(residue, branch)` pairs from edges
- [ ] `PathValidFrom` lemmas apply without issue
- [ ] Both directions of ↔ proven
- [ ] No sorries remain
- [ ] No sorry in lemmas used by Tier 3

---

## Why This Lemma Matters

**path_lifting is CRITICAL because it:**

1. **Connects two worlds:**
   - Left side: arithmetic odd-block sequences (what Lemma 7 works with)
   - Right side: graph paths (what DP certificate covers)

2. **Enables Tier 3 DP proof:**
   - Once we know paths ↔ sequences
   - We can prove all sequences satisfy DP bound
   - Therefore all paths satisfy bound

3. **Completes the bridge:**
   - Lemma 1 (TIER 2a): Edge/weight infrastructure
   - Lemma 3 (TIER 2c): Path lifting ← YOU ARE HERE
   - Lemma 2 (partial): Window properties (already have)
   - DP Coverage (TIER 3): All paths bounded

---

## Key Insight for Implementation

**The path encodes the sequence; extraction is structural:**

```lean
-- Path structure:
PathLen L :=
  { edges : [e_0, e_1, ..., e_{L-1}]
    valid : e_0.src = start,
            e_1.src = e_0.dst,
            e_2.src = e_1.dst,
            ...
  }

-- Arithmetic sequence is literally:
odd_steps := [(e_0.src.residue, e_0.src.branch),
              (e_1.src.residue, e_1.src.branch),
              ...
              (e_{L-1}.src.residue, e_{L-1}.src.branch)]

-- The "proof" is just: they're the same thing!
-- Path chaining ensures state-to-residue-pair correspondence
```

This is why the proof should be relatively straightforward: you're proving that a structural fact about paths corresponds to the arithmetic sequence they encode.

---

## When You Finish Tier 2c

You'll be ready for Tier 3:

```lean
-- The final piece: DP coverage
lemma dp_coverage (p : PathLen 16) :
  reachable p.start → weightSum p ≥ 29
```

Which you can prove by:
1. Use `path_lifting` to get the arithmetic sequence
2. Apply DP certificate (proved separately, e.g., #eval)
3. Conclude: all reachable sequences satisfy bound
4. Therefore all reachable paths satisfy bound

---

## File Locations

- **Where to add:** [src/CollatzAutomaton/Lemma8_DensityFloor.lean](src/CollatzAutomaton/Lemma8_DensityFloor.lean)
- **Or in new:** [src/CollatzAutomaton/Lemma2_PathLifting.lean](src/CollatzAutomaton/Lemma2_PathLifting.lean) (up to you)
- **Use from:** [src/CollatzAutomaton/Path.lean](src/CollatzAutomaton/Path.lean)
- **Helpers from:** [src/CollatzAutomaton/Graph.lean](src/CollatzAutomaton/Graph.lean)

---

## Next Actions

1. ✅ Understand the two-way equivalence
2. ✅ Plan proof by structural induction on `p.edges`
3. ✅ Extract `(residue, branch)` from each edge via `e.src`
4. ✅ Use `PathValidFrom.head_*` lemmas for path validity
5. ✅ Prove both directions of the ↔
6. ✅ Verify no axioms
7. ✅ Submit for Tier 3

**Estimated time: 2-3 hours of focused proof work**

Good luck! You're one theorem away from being able to prove the final DP bound.
