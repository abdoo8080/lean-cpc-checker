import Checker

open Lean

unsafe def main (args : List String) : IO Unit := do
  let query ← IO.FS.readFile args[0]!
  let t0 ← IO.monoMsNow
  initSearchPath (← findSysroot)
  withImportModules #[`Smt, `Smt.Rat] Options.empty 0 fun env => do
    let t1 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] load: {t1 - t0}"
    let coreContext := { fileName := "cpc-checker", fileMap := default }
    let coreState := { env }
    _ ← Meta.MetaM.toIO (Checker.runSolveAndCheck query) coreContext coreState
