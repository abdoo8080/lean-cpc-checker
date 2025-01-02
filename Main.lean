import Checker

open Lean

unsafe def main (args : List String) : IO Unit := do
  let t0 ← IO.monoMsNow
  initSearchPath (← findSysroot)
  let query ← IO.FS.readFile args[0]!
  let t1 ← IO.monoMsNow
  IO.println (t1 - t0)
  withImportModules #[`Smt, `Smt.Real] Options.empty 0 fun env => do
    let t2 ← IO.monoMsNow
    IO.println (t2 - t1)
    let coreContext := { fileName := "cpc-checker", fileMap := default }
    let coreState := { env }
    _ ← Meta.MetaM.toIO (runSolveAndCheck query) coreContext coreState
