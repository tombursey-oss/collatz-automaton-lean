import CollatzAutomaton.Core
import CollatzAutomaton.Graph

namespace CollatzAutomaton

/-- A path is valid if each edge is in the global edge list,
    and edges chain correctly from the given start state. -/
def PathValidFrom (start : State) : List Edge → Prop
  | [] => True
  | e :: es =>
      e ∈ edges ∧ e.src = start ∧ PathValidFrom e.dst es

/-- A path of exactly L edges with proof that it's valid. -/
structure PathLen (L : Nat) where
  start : State
  edges : List Edge
  len_eq : edges.length = L
  valid : PathValidFrom start edges

/-- Sum the weights of all edges in a path. -/
def weightSum {L : Nat} (p : PathLen L) : Nat :=
  p.edges.foldl (fun acc e => acc + edgeWeight e) 0

lemma PathValidFrom.head_mem {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → e ∈ edges := by
  intro h; exact h.1

lemma PathValidFrom.head_src {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → e.src = start := by
  intro h; exact h.2.1

lemma PathValidFrom.tail_valid {start : State} {e : Edge} {es : List Edge} :
  PathValidFrom start (e :: es) → PathValidFrom e.dst es := by
  intro h; exact h.2.2

end CollatzAutomaton
