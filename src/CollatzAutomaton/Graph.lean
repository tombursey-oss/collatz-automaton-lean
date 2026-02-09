import CollatzAutomaton.Core
import CollatzAutomaton.Data.ExpandedEdgesV2

namespace CollatzAutomaton

open CollatzAutomaton.Data

def MOD : Nat := 64

def natToBranch (b : Nat) : Branch :=
  b % 2 = 1

def mkState (r : Nat) (b : Nat) : State :=
  { residue := r, branch := natToBranch b }

def StateOK (s : State) : Prop :=
  s.residue < MOD

def expandedEdgeToEdge (ee : ExpandedEdge) : Edge :=
  { src := mkState ee.src_residue ee.src_b
    dst := mkState ee.dst_residue ee.dst_b
    w := ee.r_val }

def edges : List Edge :=
  expandedEdgesV2.map expandedEdgeToEdge

def transitionRel (s t : State) : Prop :=
  Exists fun e : Edge =>
    List.Mem e edges ∧ e.src = s ∧ e.dst = t

def isStart (s : State) : Prop :=
  s.branch = false ∧ s.residue % 2 = 1 ∧ StateOK s

inductive reachable : State -> Prop
  | start {s : State} (h : isStart s) : reachable s
  | step  {s t : State} (h1 : reachable s) (h2 : transitionRel s t) : reachable t

end CollatzAutomaton
