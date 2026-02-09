import CollatzAutomaton.Graph

namespace CollatzAutomaton

def PathValidFrom (start : State) : List Edge -> Prop
  | [] => True
  | e :: rest =>
      List.Mem e edges ∧
      e.src = start ∧
      PathValidFrom e.dst rest

structure Path where
  start : State
  edges : List Edge
  valid : PathValidFrom start edges

end CollatzAutomaton
