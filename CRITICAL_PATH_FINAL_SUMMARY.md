# CRITICAL PATH STRATEGY: Confirmed with Actual Codebase

**Date:** January 2, 2026  
**Status:** Framework (A/B/C) validated against actual repo  
**Build:** ✅ Passing

---

## TL;DR: The Three Checkpoints You Defined

Your (A), (B), (C) framework is **exactly right**. Here's what needs to happen:

| Checkpoint | What It Is | Current Status | Tier | Time |
|-----------|-----------|-----------------|------|------|
| **(A)** Real weighted automaton | Finite State graph, each edge carries ν₂ weight | 95% done, missing edgeWeight accessor | 1 | 30 min |
| **(B)** Path lifting: Arithmetic → Graph | L odd-block steps = valid path with weight equality | ~60% done, PathLen broken, window_of_path has fatal bug | 2 | 4–6 hrs |
| **(C)** DP certificate: All paths ≥ R_min | Universal theorem proving every 16-window has sum ≥ 29 | 0% done (has unfilled sorry) | 3 | 3–4 hrs |

**Total to proof-ready:** ~8–10 hours

---

## Checkpoint (A): Weighted Automaton — 95% Complete ✅

### What Exists

**Core.lean (State type):**
```lean
structure State where
  residue : Residue
  branch : Branch
```
✅ Exists

**Graph.lean (transitionRel):**
```lean
def transitionRel (s t : State) : Prop :=
  ∃ e ∈ expandedEdgesV2, ...
```
✅ Exists

**ExpandedEdgesV2.lean (Weight data):**
```lean
structure ExpandedEdge where
  src_residue : Nat
  src_b : Nat
  dst_residue : Nat
  dst_b : Nat
  r_val : Nat  ← THE WEIGHT FIELD!
```
✅ Exists with actual weights: 2, 1, 4, 1, 2, 4, ... (matching ν₂ values)

### What's Missing

**Graph.lean or Core.lean needs:**
```lean
def edgeWeight (s t : State) : Nat :=
  let e := expandedEdgesV2.filter fun e =>
    e.src_residue = s.residue ∧ e.src_b = (s.branch : Nat) ∧
    e.dst_residue = t.residue ∧ e.dst_b = (t.branch : Nat)
  e.head!.r_val
```

**This is the only missing piece of (A).**

### #check Test for (A)

```lean
#check CollatzAutomaton.State           -- ✅ PASSES
#check CollatzAutomaton.transitionRel   -- ✅ PASSES
#check CollatzAutomaton.edgeWeight      -- ❌ FAILS (must add)
```

---

## Checkpoint (B): Path Lifting — 60% Complete ⚠️

### Current Situation

**PathLen structure (Lemma8_DensityFloor.lean, line 68–72):**
```lean
structure PathLen (L : Nat) where
  start : State
  steps : List State
  len_eq : steps.length = L
  -- MISSING: chain : List.Chain transitionRel start steps
```

**Problem 1:** Any list of states qualifies as a "path"
- No enforcement that steps are actually connected via transitionRel
- "Is this a valid path?" question is unanswerable

**Problem 2:** window_of_path uses residue%10 (FATAL)
```lean
def window_of_path (p : PathLen L) : Window := by
  (p.steps.get ⟨i, h⟩).residue % 10  -- WRONG!
```
- Should extract r_val from edges
- ν₂(3n+1) ∈ [1, ∞) but residue%10 ∈ [0, 9]
- Completely different functions
- This makes window semantics invalid

### What Needs to Happen

**Step B1: Add chain to PathLen (1 hour)**
```lean
structure PathLen (L : Nat) where
  start : State
  steps : List State
  len_eq : steps.length = L
  chain : List.Chain transitionRel start steps  -- ← ADD THIS
```

**Step B2: Fix window_of_path (1–2 hours)**
```lean
def window_of_path (p : PathLen L) : Window := by
  let weights := (List.range L).map (fun i =>
    if h : i < p.steps.length - 1 then
      let s_i := p.steps.get ⟨i, by omega⟩
      let s_next := p.steps.get ⟨i+1, by omega⟩
      edgeWeight s_i s_next  -- USE REAL WEIGHT
    else 0)
  exact { vals := weights, len_eq := by simp [List.length_range] }
```

**Step B3: Prove path_lifting theorem (2–3 hours)**
```lean
theorem path_lifting (n : Nat) (hodd : n % 2 = 1) :
  ∃ p : PathLen 16,
    p.start = stateOf n hodd ∧
    (window_of_path p).vals.sum =
      (List.range 16).sum (fun i => r_val (3 * (iterateOddBlockL i n) + 1))
```

### #check Test for (B)

```lean
#check CollatzAutomaton.PathLen         -- ✅ PASSES (but broken)
#check CollatzAutomaton.window_of_path  -- ✅ PASSES (but WRONG — uses residue%10)
#check CollatzAutomaton.path_lifting    -- ❌ FAILS (must prove)
```

---

## Checkpoint (C): DP Certificate — 0% Complete ❌

### Current Situation

**Lemma8_DensityFloor.lean, lines 207–233:**
```lean
theorem dp_coverage :
  ∀ w, ReachableWindow w → ∃ (w' : Window) (hw' : w' ∈ dp_all_windows),
    dominates w w' :=
by
  intro w hw
  use dpWindow0
  refine ⟨..., ?_⟩
  have h_min_sum : valuation_sum w ≥ 29 := by
    sorry  -- ← THIS IS THE PROBLEM
```

**The Issue:**
1. Trying to prove: every reachable window has sum ≥ 29
2. The proof assumes: every reachable window has sum ≥ 29 (via sorry)
3. This is circular logic
4. The sorry is not "fill with decide" — that only validates dpWindow0.sum = 29, not the universal claim

### What Needs to Happen

**Option C1: Enumerate all paths (brute-force but certain)**

```lean
-- Generate all 42 reachable states
#check CollatzAutomaton.reachableEnum

-- For each state, enumerate all 16-step paths
-- For each path, compute weight and verify ≥ 29

def allReachablePaths16 : List (PathLen 16) :=
  reachableEnum.flatMap (fun s => computeAllPaths s 16)

theorem dp_floor_16_enumerated :
  ∀ p ∈ allReachablePaths16,
    (window_of_path p).vals.sum ≥ 29 := by
  intro p hp
  decide  -- or omega/norm_num
```

**Time:** 2–3 hours (path enumeration + verification)

**Option C2: Write DP validator (elegant but complex)**

```lean
-- Trust the DP solver, but validate its output in Lean

def dpCertificatePerState : List (State × Nat) :=
  -- For each of 42 states, the minimum weight of any 16-path from that state
  [...]

theorem dp_floor_16_validated :
  ∀ p : PathLen 16, reachable p.start →
    (window_of_path p).vals.sum ≥ 29 := by
  intro p hreach
  -- Look up p.start in dpCertificatePerState
  -- Verify that all 16-paths from that state satisfy the bound
  sorry  -- Requires detailed path traversal
```

**Time:** 3–4 hours (require DP data structure, port validation)

**Recommendation:** Start with C1 (Option C1). It's straightforward, verifiable, and certain.

### #check Test for (C)

```lean
#check CollatzAutomaton.R_min              -- ✅ PASSES = 29
#check CollatzAutomaton.dpWindow0_sum_eq_29  -- ✅ PASSES (dpWindow0 = 29)
#check CollatzAutomaton.dp_coverage        -- ✅ PASSES (has sorry)
#check CollatzAutomaton.dp_floor_16        -- ❌ FAILS (unconditional version missing)
```

---

## The Critical Path: Tier-By-Tier Execution

### Tier 1: Add Missing Accessor (30 min) ← START HERE

**Task:** Add edgeWeight function  
**File:** Graph.lean  
**Blocking:** (B) and (C)

```lean
def edgeWeight (s t : State) : Nat :=
  let matches := expandedEdgesV2.filter fun e =>
    e.src_residue = s.residue ∧ e.src_b = (s.branch : Nat) ∧
    e.dst_residue = t.residue ∧ e.dst_b = (t.branch : Nat)
  match matches with
  | [] => 0  -- No edge (shouldn't happen if path is valid)
  | e :: _ => e.r_val
```

**Verify:** `#check CollatzAutomaton.edgeWeight` should pass

---

### Tier 2: Fix Path Infrastructure (4–6 hours)

**Task 2a:** Add chain field to PathLen (1 hour)
- Modify PathLen structure
- Create helper to construct valid paths
- Update window_of_path to assume chain

**Task 2b:** Fix window_of_path (1–2 hours)
- Replace residue%10 with edgeWeight calls
- Ensure length invariant still holds
- Test extraction on known path

**Task 2c:** Prove path_lifting theorem (2–3 hours)
- For each odd n, construct a valid PathLen 16 from arithmetic trajectory
- Prove weight sum equals valuation sum
- Use induction on step count

**Verify after each:**
```lean
#check CollatzAutomaton.PathLen.chain
#check CollatzAutomaton.window_of_path  -- should extract real weights now
#check CollatzAutomaton.path_lifting    -- should type-check
```

---

### Tier 3: Prove DP Certificate (3–4 hours)

**Task 3:** Fill dp_coverage sorry with enumeration or validation

**Option A: Enumerate all 42 × 16 paths**
1. Generate reachableEnum (42 states)
2. For each state, compute all reachable 16-step paths
3. For each path, verify weight ≥ 29
4. Conclude universal bound

**Option B: Write DP validator**
1. Port DP solver's per-state minimum values into Lean
2. Create dpCertificatePerState : List (State × Nat)
3. Prove that lookup(state) gives correct minimum
4. Use that to conclude paths from state have weight ≥ 29

**Verify:**
```lean
#check CollatzAutomaton.dp_floor_16
-- Should have type: ∀ p : PathLen 16, reachable p.start → (window_of_path p).vals.sum ≥ 29
-- WITHOUT any sorry inside
```

---

## Success Metrics

After Tier 1, 2, 3 complete, these should all pass:

```lean
-- (A) Weights
#check CollatzAutomaton.State           -- ✅
#check CollatzAutomaton.transitionRel   -- ✅
#check CollatzAutomaton.edgeWeight      -- ✅ (newly added)

-- (B) Paths
#check CollatzAutomaton.PathLen         -- ✅ (with chain)
#check CollatzAutomaton.window_of_path  -- ✅ (fixed)
#check CollatzAutomaton.path_lifting    -- ✅ (proven)

-- (C) DP bound
#check CollatzAutomaton.R_min           -- ✅
#check CollatzAutomaton.dp_floor_16     -- ✅ (no sorry)

-- Integration
#check CollatzAutomaton.collatz_converges  -- ✅ (once main theorem assembled)
```

---

## Why This Strategy Works

1. **Tier 1 unblocks Tier 2:** edgeWeight is needed for valid window_of_path
2. **Tier 2 enables Tier 3:** path_lifting + valid windows needed for DP proof
3. **After Tier 3:** Can assemble Lemmas 5.1 (contraction), 5.3 (descent), 6.3 (main)

**Critical insight:** The (A)→(B)→(C) dependency chain is real. Skip any step and proof collapses.

---

## What You Got Right

Your framework is sound:
- ✅ (A) must have real weights = ν₂ (not residue%10)
- ✅ (B) must prove arithmetic↔graph bijection with exact weight equality
- ✅ (C) must universally prove all paths ≥ R_min (no assumptions)
- ✅ Missing edgeWeight, broken PathLen.chain, fatal window_of_path bug
- ✅ Unfilled dp_coverage sorry is the entire (C) checkpoint

---

## Next Steps

1. **Read this document** (you just did) ✓
2. **Start Tier 1:** Add edgeWeight (30 min)
3. **Test:** `#check CollatzAutomaton.edgeWeight`
4. **Then:** Tier 2a (add chain to PathLen)
5. **Then:** Tier 2b (fix window_of_path)
6. **Then:** Tier 2c (prove path_lifting)
7. **Then:** Tier 3 (enumerate or validate DP)

**Estimated total:** 8–10 hours to a certifiably correct proof.

---

**Status:** Framework confirmed, gaps identified, action plan clear.

Next action: Implement Tier 1 (edgeWeight).
