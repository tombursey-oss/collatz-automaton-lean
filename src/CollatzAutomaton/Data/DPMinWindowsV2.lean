namespace CollatzAutomaton.Data

/-- dp_min_windows_v2.csv rows -/
structure DPMinStep where
  window_id : Nat
  start_residue : Nat
  start_b : Nat
  step_index : Nat
  residue : Nat
  valuation : Nat

def dpMinWindowsV2 : List DPMinStep := [
  { window_id := 0, start_residue := 27, start_b := 0, step_index := 0, residue := 27, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 1, residue := 41, valuation := 2 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 2, residue := 31, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 3, residue := 47, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 4, residue := 7, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 5, residue := 43, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 6, residue := 33, valuation := 2 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 7, residue := 25, valuation := 2 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 8, residue := 19, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 9, residue := 29, valuation := 3 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 10, residue := 11, valuation := 1 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 11, residue := 17, valuation := 2 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 12, residue := 13, valuation := 3 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 13, residue := 5, valuation := 4 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 14, residue := 1, valuation := 2 }
  , { window_id := 0, start_residue := 27, start_b := 0, step_index := 15, residue := 1, valuation := 2 }
]

end CollatzAutomaton.Data
