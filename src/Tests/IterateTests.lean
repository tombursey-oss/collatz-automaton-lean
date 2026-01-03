import CollatzAutomaton.Core
import Std

open CollatzAutomaton
open Std

def expectEqual (name : String) (got expected : List Nat) : IO Unit := do
  if got == expected then
    IO.println s!"PASS: {name}"
  else
    IO.println s!"FAIL: {name} got {got} expected {expected}"

def runIterateTests : IO Unit := do
  expectEqual "iterate 3" (iterate 3) [3,10,5,16,8,4,2,1]
  expectEqual "iterate 5" (iterate 5) [5,16,8,4,2,1]
  -- check 27 ends at 1
  let seq27 := iterate 27
  let last27 := seq27.get? (seq27.length - 1)
  match last27 with
  | some x => if x == 1 then IO.println "PASS: iterate 27 ends with 1" else IO.println s!"FAIL: iterate 27 ends with {x}"
  | none => IO.println "FAIL: iterate 27 returned empty"

#eval runIterateTests
