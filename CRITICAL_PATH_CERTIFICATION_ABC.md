# CRITICAL PATH CERTIFICATION: (A), (B), (C) Mapping

**Date:** January 2, 2026  
**Purpose:** Verify the three critical checkpoints against actual repo definitions  
**Status:** ⚠️ GAPS IDENTIFIED (A/B complete structurally, C incomplete, B/C unvalidated)

---

## Your Framework: (A), (B), (C) Explained ✅ CONFIRMED

### (A) Real Weighted Automaton Matching Collatz Odd-Block Steps

**What it means:**
- Finite State space + transitionRel derived from CSV edges
- Each edge carries a weight = actual valuation ν₂(3n+1)
- Paths are enforced (not just arbitrary state lists)

**Where it belongs:** Core.lean (types/weights) + Graph.lean (paths/reachability)

### (B) Path-Lifting Lemma: Arithmetic Trajectory → Graph Path

**What it means:**
- For odd n, L odd-block steps induce valid path p : PathLen L starting at stateOf n
- weightSum p = Σ r_val(3·n_i + 1) (exact equality)
- This is **the first bridge-critical lemma**

**Where it belongs:** Lemma8_DensityFloor.lean or Lemma_PathLifting.lean

### (C) DP/Certificate Lemma: All Relevant Paths Have Weight ≥ R_min

**What it means:**
- For all length-L paths in relevant domain (all starts, or all reachable starts)
- weightSum p ≥ R_min (e.g., 29 for L=16)
- Proven **unconditionally** (not assuming what needs proving)
- This is **the second bridge-critical lemma**

**Where it belongs:** Lemma8_DensityFloor.lean (as universal theorem, not as sorry)

---

## CHECKPOINT (A): Weighted Automaton — Current Status

### ✅ Core.lean Definitions

**File:** [src/CollatzAutomaton/Core.lean](src/CollatzAutomaton/Core.lean), lines 1–57

```lean
abbrev Residue := Nat
abbrev Branch := Bool

structure State where
  residue : Residue
  branch  : Branch
  deriving Repr, DecidableEq

def Transition := State → State
def TransitionRel := State → State → Prop
def Valuation := State → Nat
abbrev ℝ := Float
def EdgeWeight := Transition → ℝ
```

**Status:** ✅ **Sufficient**
- State type exists ✓
- Transition/TransitionRel defined ✓
- EdgeWeight type alias exists ✓

### ✅ ExpandedEdgesV2 Data Structure

**File:** [src/CollatzAutomaton/Data/ExpandedEdgesV2.lean](src/CollatzAutomaton/Data/ExpandedEdgesV2.lean), lines 1–81

```lean
structure ExpandedEdge where
  src_residue : Nat
  src_b : Nat
  dst_residue : Nat
  dst_b : Nat
  transition_type : String
  r_val : Nat           -- ← WEIGHT FIELD EXISTS!
  branch : String

def expandedEdgesV2 : List ExpandedEdge := [
  { src_residue := 1, src_b := 0, dst_residue := 1, dst_b := 0, 
    transition_type := "thick", r_val := 2, branch := "det" }
  , ...
]
```

**Status:** ✅ **Correct**
- ExpandedEdge has `r_val : Nat` field ✓
- r_val is populated with actual valuations (2, 1, 4, 1, 2, 4, ...) ✓
- These values appear to match ν₂(3n+1) for the transitions ✓

### ✅ Graph.lean TransitionRel

**File:** [src/CollatzAutomaton/Graph.lean](src/CollatzAutomaton/Graph.lean), lines 1–80

```lean
def Edge := ExpandedEdge

def transitionRel (s t : State) : Prop :=
  ∃ e ∈ expandedEdgesV2,
    s.residue = e.src_residue ∧ s.branch = (e.src_b = 1) ∧
    t.residue = e.dst_residue ∧ t.branch = (e.dst_b = 1)
```

**Status:** ✅ **Correct**
- transitionRel uses ExpandedEdge.r_val implicitly ✓
- Each transition comes with its weight field ✓

### ⚠️ MISSING: edgeWeight Function (A1)

**Required:** A function to extract weight from a transition

```lean
-- MISSING IN REPO:
def edgeWeight (s t : State) : Nat :=
  let e := (expandedEdgesV2.filter fun e => 
    e.src_residue = s.residue ∧ e.src_b = (s.branch : Nat) ∧
    e.dst_residue = t.residue ∧ e.dst_b = (t.branch : Nat)).head!
  e.r_val
```

**Critical?** YES. Without this, you cannot write weightSum.

**Impact:** (A) is ~95% complete, missing only the accessor function.

---

## CHECKPOINT (B): Path-Lifting Lemma — Current Status

### ⚠️ MISSING: PathLen with Chain (B1)

**Current Definition (Lemma8_DensityFloor.lean, line 68–72):**

```lean
structure PathLen (L : Nat) where
  start : State
  steps : List State
  len_eq : steps.length = L
```

**Problem:** No `chain : List.Chain transitionRel start steps` field

This means any list of states qualifies as a "path". The length is checked but transitions are not enforced.

**Required Fix:**

```lean
structure PathLen (L : Nat) where
  start : State
  steps : List State
  len_eq : steps.length = L
  chain : List.Chain transitionRel start steps  -- ← ADD THIS
```

**Impact:** Without chain, path semantics are broken.

### ⚠️ BROKEN: window_of_path Uses residue%10 (FATAL) (B2)

**Current Definition (Lemma8_DensityFloor.lean, lines 89–99):**

```lean
def window_of_path (p : PathLen L) : Window := by
  have h_vals : (List.range L).map (fun i => 
    if h : i < p.steps.length then (p.steps.get ⟨i, h⟩).residue % 10 else 0
    -- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    -- THIS IS WRONG
  ).length = L
```

**Problem:** Uses `residue % 10` instead of extracting edge weight from transitionRel

This is a fatal bug. The function must extract r_val from edges, not compute residue%10.

**Required Fix:**

```lean
def window_of_path (p : PathLen L) : Window := by
  let weights : List Nat := 
    (List.range L).map (fun i =>
      if h : i < p.steps.length then
        let s := p.steps.get ⟨i, h⟩
        let s_next := p.steps.get ⟨i+1, by omega⟩
        edgeWeight s s_next  -- Use the weight function
      else 0)
  exact { vals := weights, len_eq := by simp [List.length_range] }
```

**Impact:** BLOCKS everything. Cannot write valid path-lifting lemma without this.

### ❌ MISSING: path_lifting Theorem (B3)

**Required Statement:**

```lean
theorem path_lifting (n : Nat) (hodd : n % 2 = 1) (L : Nat) :
  ∃ p : PathLen L,
    p.start = stateOf n hodd ∧
    valuation_sum (window_of_path p) = 
      (List.range L).sum (fun i => r_val (3 * (iterateOddBlockL i n) + 1))
```

**Current Status:** NOT FORMALIZED
- Lemmas like `reachable_path_yields_reachable_window` exist but are too weak
- No explicit path construction from arithmetic trajectory
- No weight equality proof

**Critical?** YES. This is **bridge lemma (B)**.

---

## CHECKPOINT (C): DP Certificate Lemma — Current Status

### ✅ R_min Definition (C1)

**File:** [Lemma8_DensityFloor.lean](src/CollatzAutomaton/Lemma8_DensityFloor.lean), lines 114–119

```lean
def R_min : Nat := 29

def dpWindow0 : Window :=
  { vals := [1,2,1,1,1,1,2,2,1,3,1,2,3,4,2,2]
  , len_eq := by rfl
  }
```

**Status:** ✅ R_min defined as 29 ✓

### ✅ DP Window Computation (C2)

```lean
theorem dp_window0_sum_eq_29 : valuation_sum dpWindow0 = 29 := by
  simp [valuation_sum]
```

**Status:** ✅ Window sum verified ✓

### ⚠️ CRITICAL: dp_coverage Has Unfilled Sorry (C3)

**File:** [Lemma8_DensityFloor.lean](src/CollatzAutomaton/Lemma8_DensityFloor.lean), lines 195–233

```lean
theorem dp_coverage :
  ∀ w, ReachableWindow w → ∃ (w' : Window) (hw' : w' ∈ dp_all_windows), dominates w w' :=
by
  intro w hw
  obtain ⟨p, hp_reachable, hp_window⟩ := hw
  use dpWindow0
  refine ⟨by simp [dp_all_windows], ?_⟩
  unfold dominates
  have h_min_sum : valuation_sum w ≥ 29 := by
    -- This is the crux: the DP certificate guarantees that no reachable path
    -- can have valuation sum < 29. By definition of ReachableWindow, w arises
    -- from a reachable path, so its sum is ≥ 29.
    -- In a fully machine-checked proof, this would enumerate all reachable paths
    -- or use the DP certificate data structure to validate the bound.
    sorry  -- ← UNFILLED
  calc
    valuation_sum w ≥ 29 := h_min_sum
    _ = valuation_sum dpWindow0 := (dp_window0_sum_eq_29).symm
```

**Problem:**
1. The step `valuation_sum w ≥ 29` is **assumed**, not proven
2. Replacing with `decide` doesn't help — that only validates dpWindow0.sum = 29
3. Need to prove: ∀ paths from 42 reachable states, weight ≥ 29

**Required Fix Option 1: Enumerate All Paths**

```lean
-- Enumerate all (42 reachable states) × (16 steps) = 672 paths
-- For each, compute weight and verify ≥ 29

def allReachablePaths16 : List (PathLen 16) := 
  reachableEnum.flatMap (fun s => 
    [compute all 16-step paths starting from s])

theorem dp_coverage_enumerated :
  ∀ p ∈ allReachablePaths16, valuation_sum (window_of_path p) ≥ 29 := by
  intro p hp
  -- For each path, verify explicitly
  decide  -- or omega/norm_num
```

**Required Fix Option 2: Validate DP Certificate**

```lean
-- Trust the DP solver's output and validate it in Lean

def dpCertificate : List (State × Nat) := [
  (state₁, minWeight₁), 
  (state₂, minWeight₂), 
  ...
  (state₄₂, minWeight₄₂)
]

theorem dp_certificate_correct :
  ∀ s ∈ reachableEnum, 
    ∃ w ∈ dpCertificate, 
      w.1 = s ∧ 
      (∀ p : PathLen 16, p.start = s → valuation_sum (window_of_path p) ≥ w.2)
```

**Current Status:** ❌ COMPLETELY UNFILLED
- This is the linchpin of (C)
- Without it, the universal claim is not proven

**Critical?** YES. This is **bridge lemma (C)**.

---

## The Minimal Certification #check Suite

Here's what should exist in your repo for a **real, provable proof**:

```lean
-- (A) Weights exist
#check CollatzAutomaton.State                    -- ✅ exists
#check CollatzAutomaton.transitionRel            -- ✅ exists
#check CollatzAutomaton.edgeWeight               -- ❌ MISSING

-- (B) Path structure exists with chain
#check CollatzAutomaton.PathLen                  -- ✅ exists (but no chain field)
#check CollatzAutomaton.window_of_path           -- ❌ uses residue%10 (WRONG)
#check CollatzAutomaton.stateOf                  -- ✅ likely exists
#check CollatzAutomaton.path_lifting             -- ❌ MISSING

-- (C) DP bound exists and is unconditional
#check CollatzAutomaton.R_min                    -- ✅ exists = 29
#check CollatzAutomaton.dp_coverage              -- ✅ exists but HAS SORRY
#check CollatzAutomaton.dp_floor_16              -- ❌ MISSING (unconditional version)

-- Downstream integration
#check CollatzAutomaton.collatz_converges        -- ❌ MISSING (main theorem)
```

---

## Red Flags in My Specification Document

You identified these correctly:

### 1. ❌ Lemma 0.1 includes nonsensical "< ω"

**What I wrote:**
```lean
lemma iterate_k_well_founded (n : ℕ) : ∀ k, iterate_k k n < ω := by
```

**Why it's nonsense:**
- ω (omega) is not defined in Core.lean
- This is not how you prove termination in Lean4
- Should be: define a measure and use WF recursion

**Fix:** Remove or replace with measure-based WF proof

---

### 2. ❌ PathLen lacks chain property

**What I said:** "PathLen structure" with only length invariant

**Why it's wrong:**
- Any list of states qualifies as a "path"
- You can't enforce that consecutive states are connected
- DP floor becomes meaningless

**Fix:** Add `chain : List.Chain transitionRel start steps` field

---

### 3. ❌ References to undefined objects

**Examples:**
- `edge_weight s` (function not defined)
- `iterate_oddBlock_L` (not in actual codebase)
- `construct_path_from_trajectory` (not real)
- `total_valuation_sum` (not explicit)

**Why it matters:**
- These are placeholders I invented
- The actual codebase doesn't have them
- My spec is describing what *should* exist, not what does

**Fix:** Ground spec in actual function names from repo

---

### 4. ❌ Lemma 3.2 (dp_coverage) Logic is Circular

**What I showed:**
```lean
have h_min_sum : valuation_sum w ≥ 29 := by sorry
```

**Why it's circular:**
- I'm trying to prove: every reachable window has sum ≥ 29
- The proof assumes: every reachable window has sum ≥ 29 (via sorry)
- Filling with `decide` only validates dpWindow0.sum = 29, not the universal claim

**Fix:** Actually enumerate and check all 42 × 16 paths, or write a DP validator

---

### 5. ❌ Lemma 3.3 makes "reachable" Trivial

**What I said:**
```lean
lemma reachability_coverage (n : ℕ) (h : n % 2 = 1) :
  reachable (stateOf n h) := by
  intro n h
  apply reachable.start
```

**Why it's wrong:**
- If stateOf(n) is always in isStart, then every odd integer is a "start state"
- Then "reachable" = "start states" (trivial closure)
- But your DP only checked 42 states, not all odd residues
- Scope mismatch: "reachable from DP" vs "reachable from any odd n"

**Fix:** Clarify whether stateOf maps all odd n to 42 enumerated states, or to a larger set

---

## Your Assessment: HIGHLY ACCURATE ✅

You correctly identified all major gaps:

| Issue | Severity | My Spec? | Repo Reality? |
|-------|----------|----------|---------------|
| edgeWeight function missing | CRITICAL (A1) | Not mentioned | Needs to be added |
| PathLen needs chain field | CRITICAL (B1) | ❌ Overlooked | Missing |
| window_of_path uses residue%10 | FATAL (B2) | ❌ Didn't catch | Confirmed bug |
| path_lifting theorem missing | CRITICAL (B3) | ⚠️ Vague | Not implemented |
| dp_coverage has unfilled sorry | CRITICAL (C3) | ⚠️ Acknowledged | Confirmed |
| Circular logic in DP proof | CRITICAL (C) | ❌ Didn't catch | Confirmed |
| Scope confusion on "reachable" | CRITICAL (C) | ⚠️ Vague | Likely issue |

---

## What Actually Needs to Happen: Revised Action Plan

### Tier 1: Fix Checkpoint (A) — Weighted Automaton

**Task A1:** Add edgeWeight function to Core.lean or Graph.lean
```lean
def edgeWeight (s t : State) : Nat :=
  (expandedEdgesV2.filter fun e =>
    e.src_residue = s.residue ∧ e.src_b = (s.branch : Nat) ∧
    e.dst_residue = t.residue ∧ e.dst_b = (t.branch : Nat)
  ).head!.r_val
```

**Time:** 30 min
**Blocking:** Everything downstream

### Tier 2: Fix Checkpoint (B) — Path-Lifting

**Task B1:** Add chain field to PathLen
```lean
structure PathLen (L : Nat) where
  start : State
  steps : List State
  len_eq : steps.length = L
  chain : List.Chain transitionRel start steps
```

**Time:** 1 hour (need chain-construction helpers)

**Task B2:** Fix window_of_path to extract real weights
```lean
def window_of_path (p : PathLen L) : Window := by
  let weights := (List.range L).map (fun i =>
    if h : i < p.steps.length then
      edgeWeight (p.steps.get ⟨i, h⟩) (p.steps.get ⟨i+1, ...⟩)
    else 0)
  ...
```

**Time:** 1–2 hours

**Task B3:** Prove path_lifting theorem
```lean
theorem path_lifting (n : Nat) (hodd : n % 2 = 1) :
  ∃ p : PathLen 16, 
    p.start = stateOf n hodd ∧
    valuation_sum (window_of_path p) = 
      (List.range 16).sum (fun i => r_val (3 * (iterateOddBlockL i n) + 1))
```

**Time:** 2–3 hours

**Total B:** 4–6 hours

### Tier 3: Fix Checkpoint (C) — DP Coverage

**Task C1:** Enumerate all 42 × 16 paths and verify each has weight ≥ 29

OR

**Task C2:** Write a DP certificate validator that proves minimum = 29

**Time:** 3–4 hours (C1 is brute-force but certain; C2 is elegant but complex)

---

## Next Immediate Actions

1. **Read this certification document** (10 min) ✓
2. **Examine edgeWeight definition** (5 min) — Verify if it exists, if not create stub
3. **Check if PathLen.chain exists** (5 min) — Add if missing
4. **Test window_of_path** (30 min) — Identify the actual weight extraction bug
5. **Write edgeWeight implementation** (1 hour)
6. **Fix window_of_path** (1–2 hours)

**After this, (A) and (B) will be structurally sound.**

**Then focus on (C) with enumeration or validation.**

---

## Verification

Your framework is exactly correct. Your analysis caught every major issue. My specification document was:

- ✅ Correct on architecture
- ❌ Wrong on what actually exists in repo
- ⚠️ Vague on critical details (chain, edgeWeight, path_lifting)
- ❌ Missed the residue%10 bug until you pointed it out

This certification document is grounded in actual code. It should serve as a more accurate roadmap than my spec.

