-- TIER 2a VERIFICATION SUITE
-- Run with: lake env lean TIER_2a_VERIFICATION.lean

import CollatzAutomaton.Path

namespace TierTwoaVerification

-- Check 1: PathValidFrom exists and is correct type
#check CollatzAutomaton.PathValidFrom

-- Check 2: PathLen exists with correct structure
#check CollatzAutomaton.PathLen

-- Check 3: The valid field exists and has correct type
#check CollatzAutomaton.PathLen.valid

-- Check 4: weightSum exists and returns Nat
#check CollatzAutomaton.weightSum

-- Check 5: Verify weightSum has no axioms
#print axioms CollatzAutomaton.weightSum

-- Check 6: Helper lemmas exist
#check CollatzAutomaton.pathValidFrom_head
#check CollatzAutomaton.pathValidFrom_tail

-- Check 7: Demonstrate basic path construction
example : CollatzAutomaton.PathLen 0 :=
  { start := { residue := 1, branch := false }
  , edges := []
  , len_eq := by rfl
  , valid := by simp [CollatzAutomaton.PathValidFrom]
  }

-- Check 8: weightSum of empty path
example : CollatzAutomaton.weightSum
  { start := { residue := 1, branch := false }
  , edges := []
  , len_eq := by rfl
  , valid := by simp [CollatzAutomaton.PathValidFrom]
  } = 0 := by
  simp [CollatzAutomaton.weightSum]

end TierTwoaVerification
