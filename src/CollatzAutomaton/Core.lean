/- Basic core types for the Collatz automaton.
   This module encodes the requested types:
   - `Residue` (Fin 64)
   - `Branch` (Fin 2)
   - `State` (structure with residue and branch)
   - `Transition` and `TransitionRel`
   - `Valuation` (State → Nat)
   - `EdgeWeight` (Transition → ℝ), with `ℝ` aliased to `Float` here
-/

namespace CollatzAutomaton

open Std


/- A residue class: we use `Nat` for easier construction from data files.
  If you prefer a bounded `Fin 64` type, swap this back and add proofs
  where needed. -/
abbrev Residue := Nat

/- Branch: two possibilities. Use `Bool` (false := 0, true := 1) for simplicity. -/
abbrev Branch := Bool

/- Machine state: residue plus branch. -/
structure State where
  residue : Residue
  branch  : Branch
deriving Repr, DecidableEq

/- A graph edge in the Collatz automaton.
   Each edge represents one odd-block step from source state to destination state.
   The weight `w` is the 2-adic valuation ν₂(3n+1) for that step.
-/
structure Edge where
  src : State       -- source state
  dst : State       -- destination state
  w   : Nat         -- weight: the r_val / 2-adic valuation
deriving Repr, DecidableEq

/- Extract the weight (valuation) from an edge. -/
def edgeWeight (e : Edge) : Nat := e.w

/- A deterministic transition: maps a `State` to the next `State`. -/
def Transition := State → State

/- Or, as a relation (non-deterministic / relational transitions). -/
def TransitionRel := State → State → Prop

/- Valuation assigns a natural number to each state (e.g., your `r_val` column). -/
def Valuation := State → Nat

/- Numeric type for edge weights. Mathlib's `Real` is not added here,
   so `ℝ` is aliased to `Float` as a pragmatic placeholder. Replace with
   a proper real type if you add mathlib4.
-/
abbrev ℝ := Float

/- Legacy: Edge weights assigned to transitions (conceptual; use edgeWeight instead). -/
def EdgeWeightOld := Transition → ℝ

/- Basic Collatz sequence helpers -/

def next (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

partial def iterate (n : Nat) : List Nat :=
  if n == 1 then [1] else n :: iterate (next n)

end CollatzAutomaton
