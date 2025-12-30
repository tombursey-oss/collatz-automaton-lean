namespace CollatzAutomaton.Data

/-- Rows from expanded_edges_v2.csv -/
structure ExpandedEdge where
  src_residue : Nat
  src_b : Nat
  dst_residue : Nat
  dst_b : Nat
  transition_type : String
  r_val : Nat
  branch : String

def expandedEdgesV2 : List ExpandedEdge := [
  { src_residue := 1, src_b := 0, dst_residue := 1, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 1, src_b := 1, dst_residue := 49, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 3, src_b := 0, dst_residue := 5, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 3, src_b := 1, dst_residue := 37, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 5, src_b := 0, dst_residue := 1, dst_b := 0, transition_type := "thick", r_val := 4, branch := "det" }
  , { src_residue := 5, src_b := 1, dst_residue := 13, dst_b := 0, transition_type := "thick", r_val := 4, branch := "det" }
  , { src_residue := 7, src_b := 0, dst_residue := 11, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 7, src_b := 1, dst_residue := 43, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 9, src_b := 0, dst_residue := 7, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 9, src_b := 1, dst_residue := 55, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 11, src_b := 0, dst_residue := 17, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 11, src_b := 1, dst_residue := 49, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 13, src_b := 0, dst_residue := 5, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 13, src_b := 1, dst_residue := 29, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 15, src_b := 0, dst_residue := 23, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 15, src_b := 1, dst_residue := 55, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 17, src_b := 0, dst_residue := 13, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 17, src_b := 1, dst_residue := 61, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 19, src_b := 0, dst_residue := 29, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 19, src_b := 1, dst_residue := 61, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 21, src_b := 0, dst_residue := 1, dst_b := 0, transition_type := "thick", r_val := 6, branch := "det" }
  , { src_residue := 21, src_b := 1, dst_residue := 1, dst_b := 0, transition_type := "thick", r_val := 8, branch := "det" }
  , { src_residue := 23, src_b := 0, dst_residue := 35, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 23, src_b := 1, dst_residue := 3, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 25, src_b := 0, dst_residue := 19, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 25, src_b := 1, dst_residue := 3, dst_b := 1, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 27, src_b := 0, dst_residue := 41, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 27, src_b := 1, dst_residue := 9, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 29, src_b := 0, dst_residue := 11, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 29, src_b := 1, dst_residue := 35, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 31, src_b := 0, dst_residue := 47, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 31, src_b := 1, dst_residue := 15, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 33, src_b := 0, dst_residue := 25, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 33, src_b := 1, dst_residue := 9, dst_b := 1, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 35, src_b := 0, dst_residue := 53, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 35, src_b := 1, dst_residue := 21, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 37, src_b := 0, dst_residue := 7, dst_b := 0, transition_type := "thick", r_val := 4, branch := "det" }
  , { src_residue := 37, src_b := 1, dst_residue := 19, dst_b := 0, transition_type := "thick", r_val := 4, branch := "det" }
  , { src_residue := 39, src_b := 0, dst_residue := 59, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 39, src_b := 1, dst_residue := 27, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 41, src_b := 0, dst_residue := 31, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 41, src_b := 1, dst_residue := 15, dst_b := 1, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 43, src_b := 0, dst_residue := 1, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 43, src_b := 1, dst_residue := 33, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 45, src_b := 0, dst_residue := 17, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 45, src_b := 1, dst_residue := 41, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 47, src_b := 0, dst_residue := 7, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 47, src_b := 1, dst_residue := 39, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 49, src_b := 0, dst_residue := 37, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 49, src_b := 1, dst_residue := 21, dst_b := 1, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 51, src_b := 0, dst_residue := 13, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 51, src_b := 1, dst_residue := 45, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 53, src_b := 0, dst_residue := 5, dst_b := 0, transition_type := "thick", r_val := 5, branch := "det" }
  , { src_residue := 53, src_b := 1, dst_residue := 11, dst_b := 0, transition_type := "thick", r_val := 5, branch := "det" }
  , { src_residue := 55, src_b := 0, dst_residue := 19, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 55, src_b := 1, dst_residue := 51, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 57, src_b := 0, dst_residue := 43, dst_b := 0, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 57, src_b := 1, dst_residue := 27, dst_b := 1, transition_type := "thick", r_val := 2, branch := "det" }
  , { src_residue := 59, src_b := 0, dst_residue := 25, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 59, src_b := 1, dst_residue := 57, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 61, src_b := 0, dst_residue := 23, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 61, src_b := 1, dst_residue := 47, dst_b := 0, transition_type := "thick", r_val := 3, branch := "det" }
  , { src_residue := 63, src_b := 0, dst_residue := 31, dst_b := 1, transition_type := "thin", r_val := 1, branch := "det" }
  , { src_residue := 63, src_b := 1, dst_residue := 63, dst_b := 0, transition_type := "thin", r_val := 1, branch := "det" }
]

end CollatzAutomaton.Data
