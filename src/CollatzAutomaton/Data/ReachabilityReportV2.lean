namespace CollatzAutomaton.Data

/-- reachability_report_v2.txt -/
structure ReachabilityReport where
  expanded_edges_input : String
  start_nodes_spec : String
  dp_window_length_L : Nat
  universe_num_nodes : Nat
  universe_num_edges : Nat
  start_num_nodes : Nat
  reachable_num_nodes : Nat
  reachable_num_edges : Nat
  sha256 : List (String × String)
  scope_statement : String

def reachabilityReportV2 : ReachabilityReport :=
  { expanded_edges_input := "out\\expanded_edges_v1.csv"
  , start_nodes_spec := "B0"
  , dp_window_length_L := 16
  , universe_num_nodes := 64
  , universe_num_edges := 64
  , start_num_nodes := 32
  , reachable_num_nodes := 42
  , reachable_num_edges := 42
  , sha256 := [
      ("sha256_expanded_edges_v2", "534ec259466e594e25ff54ff9ba385338789ffec980a46a6c4cedb28bc5aa464"),
      ("sha256_reachable_nodes_v2", "95751940274c7ce2d59ab7ccfe616c6af9e2f01819e7f3928e46ac7be09e40dc"),
      ("sha256_scc_decomposition_v2", "d6afcb74d3b2059978ca3ac709d4615076673e64845836b6651b828ad185153b"),
      ("sha256_cycle_ledger_v2", "000829767a5825a534caf5b3527d3df7d80c25c3f68b6ba8c4e36605f38e3249"),
      ("sha256_cycle_drift_v2", "b08e60839832f9f7c661bd8b52411fbe6c2168e59228c46de1b29f374746e563")
    ]
  , scope_statement := "All global computations (SCCs, cycles, cycle drift, DP) are performed on the reachable subgraph."
  }

end CollatzAutomaton.Data
