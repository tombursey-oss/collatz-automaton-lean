namespace CollatzAutomaton.Data

/-- Summary statistics from basin_summary_v2.txt -/
structure BasinSummary where
  odd_residue_count : Nat
  worst_stopping_time_steps : Nat
  worst_stopping_time_n : Nat
  max_excursion_value : Nat
  max_excursion_n : Nat
  verified_all_reach_1 : Bool
  sha256 : String

def basinSummaryV2 : BasinSummary :=
  { odd_residue_count := 32
  , worst_stopping_time_steps := 112
  , worst_stopping_time_n := 55
  , max_excursion_value := 9232
  , max_excursion_n := 27
  , verified_all_reach_1 := true
  , sha256 := "538064f8c36d28182e46514e2f980c53ebbf5e729bb6bc42b97befa2195f844b"
  }

end CollatzAutomaton.Data
