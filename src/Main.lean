import CollatzAutomaton.Core
import CollatzAutomaton.Graph
import CollatzAutomaton.Path
import Std

open CollatzAutomaton
open Std

def main (args : List String) : IO Unit := do
  let n := match args.get? 0 with
    | some s => match s.toNat? with
      | some v => v
      | none => 27
    | none => 27
  -- optional second argument: limit of how many terms to print
  let limit? := match args.get? 1 with
    | some s => if s == "--summary" || s == "-s" then none else s.toNat?
    | none => none

  -- optional flag anywhere: --summary or -s
  let summary := args.any (fun s => s == "--summary" || s == "-s")

  IO.println s!"Starting at: {n}"
  let seq := iterate n

  if summary then
    let len := seq.length
    let maxVal := seq.foldl (fun m x => if x > m then x else m) 0
    IO.println s!"Length: {len}, Max: {maxVal}"
  else
    let toPrint := match limit? with
      | some l => seq.take l
      | none => seq
    for x in toPrint do
      IO.println x

  IO.println "Done."
