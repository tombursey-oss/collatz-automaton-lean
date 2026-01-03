import Mathlib.Data.Real.Basic
import CollatzAutomaton.Data.DPMinWindowsV2
import CollatzAutomaton.Data.ExpandedEdgesV2
import CollatzAutomaton.Data.EdgeWeightsV0

/- Quick numeric checks for Lemma 7: reconstruct the DP window (id 0),
   build the corresponding expanded-edge path, compute mean valuation
   and mean drift (using `edgeWeightsV0`), and `#eval` the numeric results.
-/

namespace CollatzAutomaton

open CollatzAutomaton.Data

/-- Collect residues for a given `window_id` in order of `step_index`. -/
def residues_for_window (wid : Nat) : List Nat :=
  (dpMinWindowsV2.filter (fun s => s.window_id = wid)).map (fun s => (s.step_index, s.residue)).qsort (fun a b => a.fst < b.fst).map (·.snd)

/-- Find an expanded edge matching src state (residue,branch) and dst residue. -/
def find_expanded_edge (src_res : Nat) (src_b : Nat) (dst_res : Nat) : Option ExpandedEdge :=
  expandedEdgesV2.find? fun e => e.src_residue = src_res ∧ e.src_b = src_b ∧ e.dst_residue = dst_res

/-- Build the sequence of expanded edges from the residue list and start branch.
    Returns `none` if any step is missing. -/
def build_edge_path (residues : List Nat) (start_b : Nat) : Option (List ExpandedEdge) := do
  match residues with
  | [] => some []
  | r :: rs =>
    let mut cur_res := r
    let mut cur_b := start_b
    let mut acc : List ExpandedEdge := []
    for next_res in rs do
      match find_expanded_edge cur_res cur_b next_res with
      | some e =>
        acc := acc.concat [e]
        cur_res := e.dst_residue
        cur_b := e.dst_b
      | none => return none
    pure acc

/-- Compute mean valuation from a list of valuations. -/
def mean_valuation_of_vals (vals : List Nat) : Real :=
  Real.ofNat (vals.foldl (· + ·) 0) / Real.ofNat vals.length

/-- Compute mean drift from a list of expanded edges via `edgeWeightsV0`. -/
def mean_drift_of_expanded_edges (es : List ExpandedEdge) : Option Real :=
  let ws := es.map (fun e => findEdgeWeight e.src_residue e.dst_residue e.transition_type)
  if ws.any (· = none) then none else
    let nums := ws.map (·.getD 0).toList
    some (nums.foldl (· + ·) 0 / Real.ofNat nums.length)

/-- Reconstruct valuations for window id 0 and compute stats. -/
def dp0_residues : List Nat := residues_for_window 0

def dp0_vals : List Nat := (dpMinWindowsV2.filter (fun s => s.window_id = 0)).qsort (fun a b => a.step_index < b.step_index).map (·.valuation)

def dp0_edge_path : Option (List ExpandedEdge) := build_edge_path dp0_residues 0

#eval IO.println s!"dp0 residues: {dp0_residues}"
#eval IO.println s!"dp0 valuations: {dp0_vals}"
#eval IO.println s!"mean valuation: {mean_valuation_of_vals dp0_vals}"
#eval match dp0_edge_path with
  | none => IO.println "edge path: missing"
  | some es => do
    IO.println s!"edge count: {es.length}"
    match mean_drift_of_expanded_edges es with
    | none => IO.println "mean drift: missing edge weights"
    | some d => IO.println s!"mean drift: {d}"

end CollatzAutomaton
