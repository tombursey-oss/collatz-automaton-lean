# TIER 2c: Roadmap to Path Lifting Proof

## Current State Summary

### ✅ Completed (Tier 2a + 2b + Today)

| Component | Status | Location |
|-----------|--------|----------|
| MOD, StateOK | ✅ | Graph.lean, lines 19-23 |
| PathValidFrom with e ∈ edges | ✅ | Path.lean, lines 8-11 |
| PathLen structure + helpers | ✅ | Path.lean, lines 14-35 |
| mkState, natToBranch | ✅ | Graph.lean |
| Lemma8 cleanup, import Path | ✅ | Lemma8_DensityFloor.lean |
| **NEW: stateOf function** | ✅ | Graph.lean, lines 58-65 |
| **NEW: stateOf_StateOK lemma** | ✅ | Graph.lean, lines 67-71 |
| **NEW: twoAdicValuation** | ✅ | Graph.lean, lines 73-80 |
| **NEW: arithStep function** | ✅ | Graph.lean, lines 82-86 |
| **NEW: arithWeight function** | ✅ | Graph.lean, lines 88-90 |

### ⏳ Remaining (Tier 2c)

| Task | Blocker | Effort |
|------|---------|--------|
| Verify ExpandedEdgesV2 completeness | None | 30 min |
| Verify arithmetic correctness (64 cases) | ExpandedEdgesV2 audit | 1-2 hours |
| Prove step_edge lemma | Verification passing | 1-2 hours |
| Define trajectoryPath | step_edge | 1 hour |
| Prove determinism (outgoing_unique) | step_edge | 1 hour |
| Prove weightSum_eq_valSum | trajectoryPath | 1-2 hours |
| Final: #check suite + #print axioms | weightSum_eq_valSum | 30 min |

**Total estimated time: 6-8 hours**

---

## The Mathematical Framework (Now Complete)

### Arithmetic Semantics (3 + 3 = 6 definitions)

```lean
-- State abstraction
def stateOf (n : Nat) : State :=
  { residue := n % 64, branch := (n / 64) % 2 = 1 }

-- Arithmetic step
def arithStep (n : Nat) : Nat :=
  let r := twoAdicValuation (3 * n + 1)
  (3 * n + 1) / (2 ^ r)

-- Step weight (valuation)
def arithWeight (n : Nat) : Nat :=
  twoAdicValuation (3 * n + 1)

-- 2-adic valuation (helper)
def twoAdicValuation : Nat → Nat := ...
```

### Graph Structure (Already Complete)

```lean
-- Finite edge set from ExpandedEdgesV2
def edges : List Edge := ...

-- Transition relation
def transitionRel (s t : State) : Prop :=
  ∃ e ∈ edges, e.src = s ∧ e.dst = t

-- Valid paths
def PathValidFrom (start : State) : List Edge → Prop := ...

structure PathLen (L : Nat) where
  start : State
  edges : List Edge
  len_eq : edges.length = L
  valid : PathValidFrom start edges
```

---

## The Proof Pipeline for Tier 2c

### Step 1: Audit ExpandedEdgesV2 Completeness

**Claim:** ExpandedEdgesV2 contains exactly 64 edges, one for each (residue, branch) pair.

**Verification:**
```lean
-- Extract sources from edges
#eval (expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).length
-- Expected: 64

#eval (expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).toFinset.card
-- Expected: 64 (all distinct)

-- Sample checks
#eval expandedEdgesV2.filter (fun e => e.src_residue = 1 ∧ e.src_b = 0) |>.length
-- Expected: 1 edge for residue 1, branch 0

#eval expandedEdgesV2.filter (fun e => e.src_residue = 1 ∧ e.src_b = 0) |>.[0]!
-- Expected: { src_residue := 1, src_b := 0, dst_residue := 1, dst_b := 0, r_val := 2, ... }
```

**If all pass:** ✅ Continue to Step 2  
**If any fail:** 🚫 Data issue—investigate ExpandedEdgesV2 generation

---

### Step 2: Verify Arithmetic Correctness (64 Cases)

**Claim:** For each edge (src_r, src_b) → (dst_r, dst_b, r_val), the arithmetic computation matches.

**Verification for one example:**
```lean
-- Edge data: (1, 0) → (1, 0), r_val = 2
-- Arithmetic: n = 1, arithStep(1) = (3·1+1)/2² = 1, arithWeight(1) = 2

lemma verify_edge_1_0 :
  let n := 1  -- residue with branch 0
  arithStep n = 1 ∧ 
  arithWeight n = 2 ∧
  stateOf n = { residue := 1, branch := false } ∧
  stateOf (arithStep n) = { residue := 1, branch := false } := by
  decide
```

**Verification for all 64 cases:**
```lean
-- Define a helper to verify one edge
def verify_edge (e : ExpandedEdge) : Bool :=
  -- Determine which n this edge represents
  let n0 := e.src_residue  -- For branch 0
  let n1 := e.src_residue + 64  -- For branch 1
  let n := if e.src_b = 0 then n0 else n1
  
  -- Check arithmetic
  (arithStep n % 64 = e.dst_residue) ∧
  ((arithStep n / 64) % 2 = (if e.dst_b = 0 then 0 else 1)) ∧
  (arithWeight n = e.r_val)

-- Verify all edges
#eval expandedEdgesV2.all verify_edge
-- Expected: true
```

**If true:** ✅ Continue to Step 3  
**If false:** 🚫 Data mismatch—investigate which edge fails

---

### Step 3: Prove step_edge (The Critical Lemma)

**After Steps 1-2 pass, the proof becomes mechanical:**

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  -- Case analysis on n % 128 (covers all 64 odd (residue, branch) pairs)
  -- Each case: find the corresponding edge in ExpandedEdgesV2
  interval_cases (n % 128)
  -- Case n ≡ 1 (mod 128): use verified edge (1, 0) → (1, 0), r_val = 2
  · use { src := {residue := 1, branch := false},
          dst := {residue := 1, branch := false},
          w := 2 }
    constructor
    · decide  -- Edge is in edges (by ExpandedEdgesV2 definition)
    constructor
    · decide  -- stateOf 1 = {residue := 1, branch := false}
    constructor
    · decide  -- stateOf (arithStep 1) = {residue := 1, branch := false}
    · decide  -- arithWeight 1 = 2
  -- ... (63 more cases, each similar)
  · sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry; sorry
```

**Or more elegantly with automation:**
```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  decide  -- If decidable instances are properly set up
```

---

### Step 4: Define trajectoryPath

**Given:** Arithmetic sequence n, arithStep(n), arithStep(arithStep(n)), ...

**Goal:** Lift to a valid PathLen by extracting edges from the graph

```lean
def trajectoryPath (L : Nat) (n : Nat) : PathLen L := by
  -- Iterate arithmetic step L times
  let seq : List Nat := List.replicate L n |>.mapIdx (fun i _ => ...)
  
  -- Extract edges for each step
  let es : List Edge := seq.zip (seq.drop 1) |>.map (fun (n1, n2) => ...)
  
  -- Construct PathLen
  { start := stateOf n,
    edges := es,
    len_eq := by simp; omega,
    valid := by
      -- Each edge in es is in edges (by step_edge)
      -- Each edge chains correctly (by stateOf properties)
      sorry
  }
```

---

### Step 5: Prove Determinism (outgoing_unique)

**Claim:** Each reachable state has exactly one outgoing edge.

```lean
lemma outgoing_unique (n : Nat) (hodd : n % 2 = 1) :
  ∃! e, e ∈ edges ∧ e.src = stateOf n ∧ e.dst = stateOf (arithStep n) := by
  -- Follows from step_edge + ExpandedEdgesV2 completeness
  obtain ⟨e, he_mem, he_src, he_dst, he_w⟩ := step_edge n hodd
  use e
  constructor
  · exact ⟨he_mem, he_src, he_dst⟩
  constructor
  intro e' ⟨_, he'_src, he'_dst⟩
  -- Both e and e' have the same source, so they must be the same edge
  -- (by uniqueness in ExpandedEdgesV2)
  sorry
```

---

### Step 6: Prove weightSum_eq_valSum (Lemma 3 Core)

**This is the exact weight equality (not inequality!):**

```lean
theorem weightSum_eq_valSum (L : Nat) (n : Nat) (hodd : n % 2 = 1) :
  weightSum (trajectoryPath L n) = 
    (List.range L).foldl (fun acc i => acc + arithWeight (arithIter i n)) 0
```

**Where:**
```lean
def arithIter : Nat → Nat → Nat
  | 0, n => n
  | i+1, n => arithIter i (arithStep n)
```

**Proof strategy:** Induction on L, using step_edge at each step

```lean
theorem weightSum_eq_valSum (L : Nat) (n : Nat) (hodd : n % 2 = 1) :
  weightSum (trajectoryPath L n) = 
    (List.range L).foldl (fun acc i => acc + arithWeight (arithIter i n)) 0 := by
  induction L with
  | zero =>
    simp [trajectoryPath, arithIter, weightSum]
  | succ L' ih =>
    simp [trajectoryPath, arithIter, weightSum]
    rw [List.range_succ]
    -- Use step_edge to show the edge weight matches arithWeight
    have : (trajectoryPath (L'+1) n).edges |>.head!.w = arithWeight n := by
      -- Extracted edge from step_edge has weight arithWeight n
      sorry
    rw [this]
    rw [← ih]
    ring
```

**Expected result:** Exact equality ✅ (not ≥, not ≤)

---

### Step 7: Final Verification

```lean
-- Check the key results
#check CollatzAutomaton.stateOf
#check CollatzAutomaton.stateOf_StateOK
#check CollatzAutomaton.step_edge
#check CollatzAutomaton.trajectoryPath
#check CollatzAutomaton.weightSum_eq_valSum

-- Verify no axioms
#print axioms CollatzAutomaton.weightSum_eq_valSum
-- Expected: no axioms (empty list)
```

---

## Risk Assessment

### High-Confidence (✅ Unblocked)
- stateOf definition and proof ✅
- Arithmetic function definitions ✅
- Graph structure (edges, PathLen) ✅
- Path module completeness ✅

### Medium-Confidence (⚠️ Verification Dependent)
- ExpandedEdgesV2 contains all 64 edges (probable but not yet verified)
- Each edge matches arithmetic computation (highly probable given data generation)
- step_edge can be proven mechanically (follows from above)

### Lower-Confidence (⚠️ Theorem Dependent)
- trajectoryPath can be properly lifted (depends on step_edge being provable)
- weightSum_eq_valSum is exactly equal, not just ≥ (follows from step_edge correctness)

---

## Success Criteria for Tier 2c

**Tier 2c is complete when:**

1. ✅ `step_edge` is proven (theorem exists, no sorry)
2. ✅ `trajectoryPath` is defined and well-typed
3. ✅ `weightSum_eq_valSum` is proven with exact equality
4. ✅ All three compile without axioms: `#print axioms` returns empty
5. ✅ `#check` passes for all three

**Milestones:**
- [ ] Data verification (Steps 1-2): 1-2 hours
- [ ] step_edge proof (Step 3): 1-2 hours
- [ ] trajectoryPath + determinism (Steps 4-5): 2 hours
- [ ] weightSum_eq_valSum (Step 6): 1-2 hours
- [ ] Final verification (Step 7): 30 min

**Timeline: 6-8 hours of focused work**

---

## Next Immediate Action

👉 **Start with data verification (Steps 1-2)**

```lean
-- Run these #eval commands to audit ExpandedEdgesV2
#eval (CollatzAutomaton.Data.expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).length
#eval (CollatzAutomaton.Data.expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).toFinset.card

-- If both return 64: ✅ proceed to arithmetic verification
-- Otherwise: 🚫 investigate data
```

Once data is verified, step_edge follows mechanically.

---

## Architecture Coherence Check

**Theorem**: "For all odd integers n with small trajectory, weightSum of the Collatz path equals ν₂ sum"

**Dependencies:**
```
weightSum_eq_valSum
  ← trajectoryPath (lifts arithmetic to graph)
    ← step_edge (connects arithmetic to edges)
      ← stateOf (maps integers to states)
      ← arithStep (defines arithmetic iteration)
      ← ExpandedEdgesV2 (data + verification)
```

**All links now in place.** Tier 2c is ready.
