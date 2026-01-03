namespace CollatzAutomaton.Data

/-- reachable_nodes_v2.csv -/
structure ReachableNode where
  residue : Nat
  b : Nat

def reachableNodesV2 : List ReachableNode := [
  { residue := 1, b := 0 },
  { residue := 1, b := 1 },
  { residue := 3, b := 0 },
  { residue := 3, b := 1 },
  { residue := 5, b := 0 },
  { residue := 7, b := 0 },
  { residue := 7, b := 1 },
  { residue := 9, b := 0 },
  { residue := 11, b := 0 },
  { residue := 13, b := 0 },
  { residue := 13, b := 1 },
  { residue := 15, b := 0 },
  { residue := 17, b := 0 },
  { residue := 19, b := 0 },
  { residue := 19, b := 1 },
  { residue := 21, b := 0 },
  { residue := 23, b := 0 },
  { residue := 25, b := 0 },
  { residue := 25, b := 1 },
  { residue := 27, b := 0 },
  { residue := 29, b := 0 },
  { residue := 31, b := 0 },
  { residue := 31, b := 1 },
  { residue := 33, b := 0 },
  { residue := 35, b := 0 },
  { residue := 37, b := 0 },
  { residue := 37, b := 1 },
  { residue := 39, b := 0 },
  { residue := 41, b := 0 },
  { residue := 43, b := 0 },
  { residue := 43, b := 1 },
  { residue := 45, b := 0 },
  { residue := 47, b := 0 },
  { residue := 49, b := 0 },
  { residue := 51, b := 0 },
  { residue := 53, b := 0 },
  { residue := 55, b := 0 },
  { residue := 57, b := 0 },
  { residue := 59, b := 0 },
  { residue := 61, b := 0 },
  { residue := 61, b := 1 },
  { residue := 63, b := 0 }
]

end CollatzAutomaton.Data
