# Implementing Refined State Encoding for Exact Deterministic Semantics

This document provides guidance on how to refine the state encoding to support
exact deterministic step semantics, if desired.

## Current State (Coarse Abstraction)

```lean
structure State where
  residue : Nat  -- conceptually mod 64
  branch  : Bool
```

- 128 abstract states (64 residues × 2 branches)
- Sufficient for convergence proof
- NOT deterministic for all edges

## Option 1: Fixed High Precision (Recommended for Exact Semantics)

Use the maximum precision needed by any edge in the automaton.

```lean
-- Maximum edge weight in the data is r=8, requiring mod 2^14 = 16384
abbrev MAX_EDGE_WEIGHT : Nat := 8
abbrev STATE_MODULUS : Nat := 2^(MAX_EDGE_WEIGHT + 6)  -- 2^14 = 16384

structure RefinedState where
  residue : Fin STATE_MODULUS  -- residue mod 16384
  branch  : Bool
```

### Pros
- Supports exact deterministic semantics for all edges in current data
- Relatively simple type system
- Fixed-size state space

### Cons
- Large state space: 32768 states (vs 128 in coarse abstraction)
- Reachability analysis becomes much more expensive
- Would need to rerun DP solver with refined encoding

### Required Changes
1. Update `State` definition in `Core.lean`
2. Update `transitionRel` in `Graph.lean` to use refined transitions
3. Recompute `expandedEdgesV2` and `reachableNodesV2` with mod 16384
4. Verify that all edge transitions are now deterministic
5. Prove `refined_state_is_exact` theorem

## Option 2: Variable Precision (Most General)

Allow different edges to use different precision based on their weight.

```lean
structure VariablePrecisionState (r : Nat) where
  residue : Fin (2^(r + 6))  -- mod 2^(r+6)
  branch  : Bool

-- Edge with specific weight requirement
structure TypedEdge where
  src : VariablePrecisionState r_src
  dst : VariablePrecisionState r_dst
  weight : Nat
  h_weight : weight = r_src  -- src precision matches edge weight
```

### Pros
- Minimal precision for each edge
- Theoretically elegant
- Makes precision requirements explicit in types

### Cons
- Complex dependent type system
- Difficult to compose edges with different precisions
- Requires sophisticated type-level reasoning
- May be impractical in Lean 4

## Option 3: Parametric Precision (Practical Middle Ground)

Make precision a parameter of the entire automaton.

```lean
structure CollatzAutomaton (modulus : Nat) where
  State : Type := { residue : Fin modulus // branch : Bool }
  edges : List (State × State × Nat)  -- (src, dst, weight)
  h_modulus_sufficient : ∀ e ∈ edges, modulus ≥ 2^(e.weight + 6)

def CoarseAutomaton : CollatzAutomaton 64 := ...
def RefinedAutomaton : CollatzAutomaton 16384 := ...
```

### Pros
- Clean abstraction over precision
- Can prove relationships between different precision levels
- Supports gradual refinement

### Cons
- More abstract, may complicate proofs
- Need to relate coarse and refined automatons
- Still need to recompute data for refined version

## Option 4: Keep Coarse, Add Refinement Map (Hybrid)

Keep the coarse abstraction for the main proof, add refinement as a secondary layer.

```lean
-- Original coarse state
structure CoarseState where
  residue : Nat  -- mod 64
  branch  : Bool

-- Refined state
structure RefinedState where
  residue : Fin 16384
  branch  : Bool

-- Projection map
def refine_state (s : CoarseState) : Set RefinedState :=
  { r | r.residue % 64 = s.residue ∧ r.branch = s.branch }

-- Each coarse state represents a set of refined states
-- Edges are deterministic at refined level but not coarse level
```

### Pros
- Preserves existing coarse proof
- Adds exact semantics as refinement
- Can prove coarse proof is sound by refinement

### Cons
- More complex: two state encodings to maintain
- Refinement proofs can be tedious
- Still need refined edge data

## Recommended Approach

**If you want exact deterministic semantics:**
1. Use **Option 1** (Fixed High Precision with mod 16384)
2. Rerun the computational DP solver with refined state encoding
3. Generate new `expandedEdgesV2Refined.lean` and `reachableNodesV2Refined.lean`
4. Prove that transitions are now deterministic
5. Verify convergence proof still works with refined states

**If you want to keep the current proof and just understand limitations:**
1. Use the existing coarse abstraction (already done)
2. Document the abstraction as a sound approximation (already done)
3. Add axioms making trust boundaries explicit (already done)
4. Keep Option 1 as a future enhancement if needed

## Implementation Example: Fixed High Precision

Here's a concrete implementation sketch:

```lean
-- In Core.lean
namespace CollatzAutomaton

abbrev REFINED_MODULUS : Nat := 16384  -- 2^14

structure RefinedState where
  residue : Fin REFINED_MODULUS
  branch  : Bool
deriving Repr, DecidableEq

-- Deterministic transition function
def refined_next (s : RefinedState) : RefinedState :=
  let n := s.residue.val
  if s.branch then
    -- Odd branch: compute 3n+1, extract weight
    let val := 3 * n + 1
    let weight := val.factorization 2  -- count factors of 2
    let next_val := val / (2^weight)
    { residue := ⟨next_val % REFINED_MODULUS, by ...⟩, 
      branch := (next_val % 2 = 1) }
  else
    -- Even branch: divide by 2
    { residue := ⟨n / 2, by ...⟩, 
      branch := ((n / 2) % 2 = 1) }

-- Prove determinism
theorem refined_transition_is_deterministic (s : RefinedState) :
  ∃! s', refined_next s = s' := by
  use refined_next s
  constructor
  · rfl
  · intro s' h; exact h

-- Prove it projects to coarse abstraction
def project_state (r : RefinedState) : State :=
  { residue := r.residue.val % 64, branch := r.branch }

theorem refined_respects_coarse (s : RefinedState) :
  project_state (refined_next s) = coarse_next (project_state s) := by
  sorry  -- Would need to prove this carefully

end CollatzAutomaton
```

## Testing Refined Semantics

To verify the refined encoding works, test the problematic edge:

```lean
-- Test edge (21, 1) → (1, 0) with weight 8
def test_edge_21_1 : Prop :=
  ∀ n : Fin REFINED_MODULUS,
    n.val % 64 = 21 →  -- all representatives of residue 21
    let s : RefinedState := ⟨n, true⟩  -- branch = 1
    let s' := refined_next s
    -- Either edge doesn't apply, or it goes to (1, 0) with weight 8
    (factorization_2 (3 * n.val + 1) ≠ 8) ∨ 
    (s'.residue.val = 1 ∧ s'.branch = false)

-- This will be provable with refined encoding but false with coarse encoding
```

## Conclusion

The refined state encoding is **implementable** but requires:
1. Significant effort to recompute all data at higher precision
2. Verification that determinism now holds
3. Reproving theorems with refined states

The current coarse abstraction is **sufficient** for the convergence proof and
is the pragmatic choice unless exact deterministic semantics are specifically required.

For most purposes, documenting the abstraction (as we have done) is adequate.
