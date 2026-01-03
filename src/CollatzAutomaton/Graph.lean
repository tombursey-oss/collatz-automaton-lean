import CollatzAutomaton.Core
import CollatzAutomaton.Data.ExpandedEdgesV2
import CollatzAutomaton.Data.ReachableNodesV2

/- Graph and reachability formalization for the Collatz automaton.

  - `transitionRel` is defined from the `expandedEdgesV2` data.
  - `reachable` is the inductive closure from the start set `isStart`.
  - The statements about the exact reachable set size and cycle drift
    are provided as theorems; filling the machine-checked proofs requires
    either automation or enumerating explicit chains for each reachable
    node and each cycle. Those are left as proof obligations here.
-/

namespace CollatzAutomaton

open CollatzAutomaton.Data

/-- Modulus for residue universe: restricts States to finite set. -/
def MOD : Nat := 64

/-- Predicate: a State is "ok" if its residue is in [0, MOD). -/
def StateOK (s : State) : Prop := s.residue < MOD

/-- Convert numeric branch (0/1) in CSV to `Branch` (Bool). -/
def natToBranch (b : Nat) : Branch := b % 2 = 1

/-- Convert an ExpandedEdge (CSV row) to a CollatzAutomaton.Edge. -/
def expandedEdgeToEdge (ee : Data.ExpandedEdge) : Edge :=
  { src := { residue := ee.src_residue, branch := natToBranch ee.src_b }
  , dst := { residue := ee.dst_residue, branch := natToBranch ee.dst_b }
  , w := ee.r_val
  }

/-- The complete list of edges derived from the CSV data. -/
def edges : List Edge :=
  expandedEdgesV2.map expandedEdgeToEdge

/-- The transition relation induced by the expanded edge list. -/
def transitionRel (s t : State) : Prop :=
  ∃ e ∈ edges,
    e.src = s ∧ e.dst = t

/-- Start set `B0`: branch 0 (we represent as `false`), odd residues, finite universe.
    This matches the `start_nodes_spec: B0` used in the report. -/
def isStart (s : State) : Prop :=
  s.branch = false ∧ s.residue % 2 = 1 ∧ StateOK s

/-- Inductive reachability from the start set using `transitionRel`. -/
inductive reachable : State → Prop
  | start {s} (h : isStart s) : reachable s
  | step {s t} (h₁ : reachable s) (h₂ : transitionRel s t) : reachable t

/-- Helper: lift a numeric pair into a `State`. -/
def mkState (r : Nat) (b : Nat) : State :=
  { residue := r, branch := natToBranch b }

end CollatzAutomaton
