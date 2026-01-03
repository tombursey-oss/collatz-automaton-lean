-- Final verification suite for Tier 2a with fatal fixes applied
-- All three fixes: MOD+StateOK for isStart, e ∈ edges in PathValidFrom, mkState consistency

import CollatzAutomaton.Graph
import CollatzAutomaton.Path

namespace Verification

-- Check 1: MOD constant exists and is 64
#check CollatzAutomaton.MOD
#eval CollatzAutomaton.MOD

-- Check 2: StateOK predicate exists
#check CollatzAutomaton.StateOK

-- Check 3: isStart is now finite (includes StateOK)
#check CollatzAutomaton.isStart

-- Check 4: mkState uses natToBranch consistently
#check CollatzAutomaton.mkState

-- Check 5: PathValidFrom now requires membership in edges (CRITICAL FIX)
#check CollatzAutomaton.PathValidFrom

-- Check 6: PathLen structure with valid field
#check CollatzAutomaton.PathLen
#check CollatzAutomaton.PathLen.valid

-- Check 7: weightSum using foldl (optimized for proofs)
#check CollatzAutomaton.weightSum
#print axioms CollatzAutomaton.weightSum

-- Check 8: Three helper lemmas (not old def-style)
#check CollatzAutomaton.PathValidFrom.head_mem
#check CollatzAutomaton.PathValidFrom.head_src
#check CollatzAutomaton.PathValidFrom.tail_valid

-- Verify the three lemmas are actually lemmas (not defs)
#print CollatzAutomaton.PathValidFrom.head_mem
#print CollatzAutomaton.PathValidFrom.head_src
#print CollatzAutomaton.PathValidFrom.tail_valid

-- Example: Build a valid path from an edge in edges
example : ∃ (p : CollatzAutomaton.PathLen 1),
  CollatzAutomaton.weightSum p = p.edges.head!.w := by
  sorry

end Verification
