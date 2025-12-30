namespace CollatzAutomaton.Data

/-- Rows from basin_verification_v2.csv -/
structure BasinRow where
  n : Nat
  stopping_time_steps : Nat
  max_excursion_value : Nat
  reaches_1 : Bool

def basinVerificationV2 : List BasinRow := [
  { n := 1, stopping_time_steps := 0, max_excursion_value := 1, reaches_1 := true }
  , { n := 3, stopping_time_steps := 7, max_excursion_value := 16, reaches_1 := true }
  , { n := 5, stopping_time_steps := 5, max_excursion_value := 16, reaches_1 := true }
  , { n := 7, stopping_time_steps := 16, max_excursion_value := 52, reaches_1 := true }
  , { n := 9, stopping_time_steps := 19, max_excursion_value := 52, reaches_1 := true }
  , { n := 11, stopping_time_steps := 14, max_excursion_value := 52, reaches_1 := true }
  , { n := 13, stopping_time_steps := 9, max_excursion_value := 40, reaches_1 := true }
  , { n := 15, stopping_time_steps := 17, max_excursion_value := 160, reaches_1 := true }
  , { n := 17, stopping_time_steps := 12, max_excursion_value := 52, reaches_1 := true }
  , { n := 19, stopping_time_steps := 20, max_excursion_value := 88, reaches_1 := true }
  , { n := 21, stopping_time_steps := 7, max_excursion_value := 64, reaches_1 := true }
  , { n := 23, stopping_time_steps := 15, max_excursion_value := 160, reaches_1 := true }
  , { n := 25, stopping_time_steps := 23, max_excursion_value := 88, reaches_1 := true }
  , { n := 27, stopping_time_steps := 111, max_excursion_value := 9232, reaches_1 := true }
  , { n := 29, stopping_time_steps := 18, max_excursion_value := 88, reaches_1 := true }
  , { n := 31, stopping_time_steps := 106, max_excursion_value := 9232, reaches_1 := true }
  , { n := 33, stopping_time_steps := 26, max_excursion_value := 100, reaches_1 := true }
  , { n := 35, stopping_time_steps := 13, max_excursion_value := 160, reaches_1 := true }
  , { n := 37, stopping_time_steps := 21, max_excursion_value := 112, reaches_1 := true }
  , { n := 39, stopping_time_steps := 34, max_excursion_value := 304, reaches_1 := true }
  , { n := 41, stopping_time_steps := 109, max_excursion_value := 9232, reaches_1 := true }
  , { n := 43, stopping_time_steps := 29, max_excursion_value := 196, reaches_1 := true }
  , { n := 45, stopping_time_steps := 16, max_excursion_value := 136, reaches_1 := true }
  , { n := 47, stopping_time_steps := 104, max_excursion_value := 9232, reaches_1 := true }
  , { n := 49, stopping_time_steps := 24, max_excursion_value := 148, reaches_1 := true }
  , { n := 51, stopping_time_steps := 24, max_excursion_value := 232, reaches_1 := true }
  , { n := 53, stopping_time_steps := 11, max_excursion_value := 160, reaches_1 := true }
  , { n := 55, stopping_time_steps := 112, max_excursion_value := 9232, reaches_1 := true }
  , { n := 57, stopping_time_steps := 32, max_excursion_value := 196, reaches_1 := true }
  , { n := 59, stopping_time_steps := 32, max_excursion_value := 304, reaches_1 := true }
  , { n := 61, stopping_time_steps := 19, max_excursion_value := 184, reaches_1 := true }
  , { n := 63, stopping_time_steps := 107, max_excursion_value := 9232, reaches_1 := true }
]

end CollatzAutomaton.Data
