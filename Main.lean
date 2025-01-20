import Checker

open Lean

def modules : Array Import := #[
  `Smt.Reconstruct.Builtin.Lemmas,
  `Smt.Reconstruct.Builtin.Rewrites,
  `Smt.Reconstruct.Int.Lemmas,
  `Smt.Reconstruct.Int.Polynorm,
  `Smt.Reconstruct.Int.Rewrites,
  `Smt.Reconstruct.Prop.Core,
  `Smt.Reconstruct.Prop.Lemmas,
  `Smt.Reconstruct.Prop.Rewrites,
  `Smt.Reconstruct.Quant.Lemmas,
  `Smt.Reconstruct.Rat.Core,
  `Smt.Reconstruct.Rat.Polynorm,
  `Smt.Reconstruct.Rat.Lemmas,
  `Smt.Reconstruct.Rat.Rewrites,
  -- `Smt.Reconstruct.Real.Polynorm,
  -- `Smt.Reconstruct.Real.Lemmas,
  -- `Smt.Reconstruct.Real.Rewrites,
  `Smt.Reconstruct.UF.Rewrites
]

unsafe def main (args : List String) : IO Unit := do
  let query ← IO.FS.readFile args[0]!
  let t0 ← IO.monoMsNow
  initSearchPath (← findSysroot)
  withImportModules modules Options.empty 0 fun env => do
    enableInitializersExecution
    let t1 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] load: {t1 - t0}"
    let coreContext := { fileName := "cpc-checker", fileMap := default }
    let coreState := { env }
    _ ← Meta.MetaM.toIO (Checker.runSolveAndCheck query) coreContext coreState
