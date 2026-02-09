# TIER 2c: step_edge Lemma — The Critical Bottleneck

## The Lemma to Prove

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n
```

**What this says:**
- For any odd integer n,
- There exists an edge in our finite graph
- That edge's source is the state corresponding to n
- That edge's destination is the state corresponding to oddBlock(n)
- That edge's weight equals ν₂(3n+1)

**Status:** ⏳ **READY TO PROVE** — all definitions now in place

---

## Why This Lemma Is The Bottleneck

1. **It connects arithmetic to graph**: Links the Collatz iteration (arithStep) to the automaton edges
2. **It grounds the entire tower**: All of Tier 2c depends on this being true
3. **It's non-trivial**: Requires that ExpandedEdgesV2 is:
   - Complete (covers all 64 (residue, branch) pairs)
   - Correct (maps each pair to the right arithmetic destination)
   - Consistent (all edges are well-formed)

---

## Proof Strategy Options

### Option A: Exhaustive Case Analysis (Most Direct)

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  -- Split into cases based on (n % 128) to cover all 64 (residue, branch) pairs
  interval_cases (n % 128)
  · -- Case: n ≡ 1 (mod 128)
    use { src := {residue := 1, branch := false},
          dst := {residue := 1, branch := false},
          w := 2 }
    refine ⟨by decide, ?_, ?_, ?_⟩
    · -- Verify src
      simp [stateOf, natToBranch]
      sorry  -- Show stateOf n = {residue := 1, branch := false}
    · -- Verify dst
      sorry  -- Show stateOf (arithStep n) = {residue := 1, branch := false}
    · -- Verify weight
      sorry  -- Show arithWeight n = 2
  · -- Case: n ≡ 3 (mod 128)
    sorry
  · -- ... (62 more cases)
    sorry
```

**Pros:**
- Direct and mechanical
- No heavy mathematics required
- Decidable (can in principle be automated)

**Cons:**
- 64 cases to verify
- Repetitive
- Requires explicit computation for each case

### Option B: Lookup Strategy (More Elegant)

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  -- Define a lookup function that finds the right edge
  let src_state := stateOf n
  let dst_residue := arithStep n % 64
  let dst_branch := (arithStep n / 64) % 2 = 1
  
  -- Look up the edge with matching source
  have src_in_edges : ∃ e ∈ edges, e.src = src_state := by
    -- All 64 (residue, branch) pairs appear in ExpandedEdgesV2
    sorry
  
  obtain ⟨e, he_mem, he_src⟩ := src_in_edges
  
  use e, he_mem
  refine ⟨he_src, ?_, ?_⟩
  
  -- Verify destination and weight follow from arithmetic
  · sorry  -- Show e.dst = stateOf (arithStep n)
  · sorry  -- Show e.w = arithWeight n
```

**Pros:**
- More modular
- Easier to extend or modify
- Cleaner presentation

**Cons:**
- Requires proving completeness of edge set
- May still need case analysis internally

### Option C: Compute + Verify Strategy (Hybrid)

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  -- Reduce to checking a fixed set (n % 128 in range [0, 128))
  have : n % 128 < 128 := Nat.mod_lt n (by norm_num : 0 < 128)
  
  -- Compute based on n % 128 (for odd n, this is 64 possibilities)
  omega  -- Or: decide / decidable instance / tactic_to_compute_odd_cases
```

**Pros:**
- Shortest code
- Uses decidability
- Can be verified by computation

**Cons:**
- Requires `decidable` instance for edge membership
- May be slow for large case splits

---

## Data Verification Requirements

**Before we can prove step_edge, we need to verify:**

### 1. Completeness
**Question**: Does ExpandedEdgesV2 contain exactly one edge for each (residue, branch) pair?

**Check**:
```lean
-- All 32 odd residues
def odd_residues : List Nat := [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63]

-- All 2 branches
def branches : List Bool := [false, true]

-- Verify: for each (r, b) in Cartesian product, exactly one edge in edges has src = {residue := r, branch := b}
lemma edges_complete_and_deterministic :
  ∀ r ∈ odd_residues, ∀ b ∈ branches,
    ∃! e ∈ edges, e.src.residue = r ∧ e.src.branch = b
```

**Current status**: Unknown (need to audit ExpandedEdgesV2)

### 2. Correctness
**Question**: For each edge, does the destination match arithStep computation?

**Check** (for one example edge):
```lean
-- Edge: src_residue := 1, src_b := 0 → dst_residue := 1, dst_b := 0, r_val := 2
-- Claim: 
--   - n = 1
--   - arithStep(1) = oddBlock(1) = (3·1+1)/2^2 = 4/4 = 1
--   - arithWeight(1) = ν₂(4) = 2
--   - stateOf(1) = {residue := 1, branch := false}
--   - stateOf(arithStep(1)) = stateOf(1) = {residue := 1, branch := false}

lemma example_edge_1 :
  let n := 1
  arithStep n = 1 ∧ 
  arithWeight n = 2 ∧
  stateOf n = {residue := 1, branch := false} ∧
  stateOf (arithStep n) = {residue := 1, branch := false} := by
  decide
```

**Strategy**: Compute one example for each (residue, branch) pair to verify correctness

### 3. Consistency
**Question**: Do all edges satisfy the invariants?

**Checks**:
```lean
-- (a) All sources are valid states (StateOK)
lemma all_edges_src_valid : ∀ e ∈ edges, StateOK e.src

-- (b) All destinations are valid states (StateOK)
lemma all_edges_dst_valid : ∀ e ∈ edges, StateOK e.dst

-- (c) All weights are positive
lemma all_edges_weight_positive : ∀ e ∈ edges, 0 < e.w

-- (d) All weights match arithmetic (this is step_edge itself!)
```

---

## Recommended Approach for Tier 2c

### Phase 1: Audit ExpandedEdgesV2 (30 min - 1 hour)

Create a checklist verifying:

```lean
#eval (expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).length  -- Should be 64

#eval (expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).toFinset.card  -- Should be 64 (all distinct)

-- Check no duplicate sources
#eval (expandedEdgesV2.map (fun e => (e.src_residue, e.src_b))).permutations.length == 1

-- Check a few examples
#eval (expandedEdgesV2.filter (fun e => e.src_residue = 1 && e.src_b = 0)).length  -- Should be 1
#eval (expandedEdgesV2.filter (fun e => e.src_residue = 1 && e.src_b = 0))[0]!.dst_residue  -- Should be 1
#eval (expandedEdgesV2.filter (fun e => e.src_residue = 1 && e.src_b = 0))[0]!.r_val  -- Should be 2
```

### Phase 2: Verify Arithmetic Computations (1-2 hours)

For each edge, compute:
```lean
-- For n = residue (if branch = 0) or n = residue + 64 (if branch = 1)
-- Verify: (3n + 1) / 2^{ν₂(3n+1)} ≡ dst_residue (mod 64)
-- Verify: ν₂(3n+1) = r_val
```

Create a helper:
```lean
def verify_edge (src_residue dst_residue src_b r_val : Nat) : Bool :=
  let n := if src_b = 0 then src_residue else src_residue + 64
  let computed_arith_step := arithStep n
  let computed_weight := arithWeight n
  computed_arith_step % 64 = dst_residue ∧
  (computed_arith_step / 64) % 2 = (if computed_weight > 8 then 0 else dst_b) ∧  -- branch check
  computed_weight = r_val

#eval expandedEdgesV2.all (fun e => verify_edge e.src_residue e.dst_residue e.src_b e.r_val)
```

### Phase 3: Prove step_edge (1-2 hours)

Once verification passes, prove:

```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  -- Case analysis on n % 128 (covering all 64 odd (residue, branch) pairs)
  interval_cases (n % 128)
  <64 cases with decide or explicit verification>
```

Or use automation:
```lean
lemma step_edge (n : Nat) (hodd : n % 2 = 1) :
  ∃ e ∈ edges,
    e.src = stateOf n ∧
    e.dst = stateOf (arithStep n) ∧
    e.w = arithWeight n := by
  decide  -- If all decidable instances are in place
```

---

## Dependency Chain for Tier 2c

```
step_edge (this lemma)
    ↓
trajectoryPath (build path from arithmetic sequence)
    ↓
weightSum_eq_valSum (prove exact weight equality)
    ↓
path_lifting (Tier 2c complete!)
    ↓
dp_floor_16 (Tier 3)
```

**step_edge is the linchpin.** Once proven, the rest follows mechanically.

---

## Status Check

- [x] Definitions added (stateOf, arithStep, arithWeight, twoAdicValuation)
- [x] stateOf_StateOK proved
- [ ] step_edge lemma stated
- [ ] ExpandedEdgesV2 completeness verified
- [ ] Arithmetic computations verified for all 64 cases
- [ ] step_edge proved

**Blockers:** None (data is available, only proof work remains)

**Next:** Verify ExpandedEdgesV2 completeness and correctness, then prove step_edge.
