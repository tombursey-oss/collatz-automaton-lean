-- TIER 1 SANITY CHECK SUITE
-- Run with: lake env lean TIER_1_SANITY_CHECK.lean

import CollatzAutomaton.Core
import CollatzAutomaton.Path

-- First, let me verify what's in Core
#check CollatzAutomaton.State
#check CollatzAutomaton.Edge
#check CollatzAutomaton.edgeWeight

-- Now try Graph items (Graph should be transitively imported via Path if needed)
#check CollatzAutomaton.transitionRel

-- ============================================================================
-- CHECK 2: Weights are Nat (not Float)
-- ============================================================================

#check CollatzAutomaton.edgeWeight
-- Expected: CollatzAutomaton.edgeWeight : CollatzAutomaton.Edge → Nat

#check CollatzAutomaton.Edge.w
-- Expected: CollatzAutomaton.Edge.w : CollatzAutomaton.Edge → Nat

-- Make sure EdgeWeightOld is not used anywhere (should be deprecated)
-- If this fails, there's a floating-point edge weight somewhere
-- #check CollatzAutomaton.EdgeWeight  -- Should NOT exist or should error

-- ============================================================================
-- CHECK 3: edges is derived from expandedEdgesV2
-- ============================================================================

#check CollatzAutomaton.edges
#print CollatzAutomaton.edges

-- ============================================================================
-- CHECK 4: Decidability instances
-- ============================================================================

#check (inferInstance : DecidableEq CollatzAutomaton.State)
#check (inferInstance : DecidableEq CollatzAutomaton.Edge)

-- Optional: Can we decide transitionRel?
-- This will be needed for Tier 3 (DP certificate)
example (s t : CollatzAutomaton.State) : Decidable (CollatzAutomaton.transitionRel s t) := by
  unfold CollatzAutomaton.transitionRel
  -- Should be decidable because edges is a finite list
  -- and membership + conjunction are decidable
  infer_instance

-- ============================================================================
-- CHECK 5: natToBranch convention (critical for State equality)
-- ============================================================================

#check CollatzAutomaton.natToBranch
#print CollatzAutomaton.natToBranch

-- Verify it's consistent: natToBranch n should be (n % 2 = 1) or (n = 1)
-- throughout the codebase

-- ============================================================================
-- CHECK 6: Edge structure is concrete
-- ============================================================================

#check CollatzAutomaton.Edge.src
#check CollatzAutomaton.Edge.dst
#check CollatzAutomaton.Edge.w

example : CollatzAutomaton.Edge :=
  { src := { residue := 0, branch := false }
  , dst := { residue := 1, branch := true }
  , w := 2
  }

-- ============================================================================
-- CHECK 7: expandedEdgeToEdge exists and is used
-- ============================================================================

#check CollatzAutomaton.expandedEdgeToEdge
#print CollatzAutomaton.expandedEdgeToEdge

-- ============================================================================
-- CHECK 8: AXIOM AUDIT — Are there any sorries/admits in core modules?
-- ============================================================================

-- This will fail if there are sorries, which is intentional
-- (we want to know about them)

-- Uncomment this to check:
-- #check @CollatzAutomaton.sorry_in_core

-- Instead, run this shell command manually:
-- rg -n "\bsorry\b|\badmit\b" src/CollatzAutomaton/Core.lean
-- rg -n "\bsorry\b|\badmit\b" src/CollatzAutomaton/Graph.lean

#print axioms CollatzAutomaton.transitionRel
-- Should print: "axioms: " with no items (no sorries)

end TierOneSanityCheck
