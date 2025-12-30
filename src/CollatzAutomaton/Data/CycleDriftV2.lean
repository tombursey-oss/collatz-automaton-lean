namespace CollatzAutomaton.Data

/-- cycle_drift_v2.csv (single-row summary) -/
structure CycleDrift where
  cycle_id : Nat
  length : Nat
  mean_drift : Float
  min_edge_weight : Float
  max_edge_weight : Float
  sum_r_val : Nat

def cycleDriftV2 : List CycleDrift :=
  [ { cycle_id := 0, length := 1, mean_drift := 0.0, min_edge_weight := 0.0, max_edge_weight := 0.0, sum_r_val := 2 } ]

end CollatzAutomaton.Data
