namespace CollatzAutomaton.Data

/-- dp_summary_v2.txt -/
structure DPSummary where
  window_length_L : Nat
  objective : String
  start_nodes_spec : String
  min_sum_r : Nat
  num_end_states_with_min : Nat
  canonical_end_state : String
  sha256 : List (String × String)

def dpSummaryV2 : DPSummary :=
  { window_length_L := 16
  , objective := "minimize sum of r_val over length-L windows on reachable subgraph"
  , start_nodes_spec := "B0"
  , min_sum_r := 29
  , num_end_states_with_min := 1
  , canonical_end_state := "(1, 0)"
  , sha256 := [
      ("sha256_dp_config_v2", "63ec6abd2782117208d422acdc6e7b488dd73e8b68c1382d646bae1f98ed433f"),
      ("sha256_dp_min_windows_v2", "75a983a98f8b8c7767984f0e62c0da9ee138c1aaea23984b993f5f7a7406eabc"),
      ("sha256_expanded_edges_v2", "534ec259466e594e25ff54ff9ba385338789ffec980a46a6c4cedb28bc5aa464"),
      ("sha256_reachability_report_v2", "9e501c545f2c0ec342bd16c75f5f26b155f94b1f442fe9c78ade168a82a78859")
    ]
  }

end CollatzAutomaton.Data
