import Smt

def IO.printlnAndFlush {α} [ToString α] (a : α) : IO Unit := do
  IO.println a
  (← IO.getStdout).flush

open Lean
open Qq

namespace Checker

def trace (r : Except Exception α) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open cvc5 in
def solve (query : String) : MetaM (Except Error Proof) := withTraceNode `solve trace do
  Solver.run (← TermManager.new) do
    Solver.setOption "incremental" "false"
    Solver.setOption "dag-thresh" "0"
    Solver.setOption "enum-inst" "true"
    Solver.setOption "cegqi-midpoint" "true"
    Solver.setOption "produce-proofs" "true"
    Solver.setOption "proof-elim-subtypes" "true"
    Solver.setOption "proof-granularity" "dsl-rewrite"
    Solver.parseCommands query
    let ps ← Solver.getProof
    if h : 0 < ps.size then
      return ps[0]
    throw (self := instMonadExceptOfMonadExceptOf _ _) (Error.error s!"Expected a proof, got none")

partial def getBoundVars (t : cvc5.Term) : Std.HashSet cvc5.Term :=
  go t {}
where
  go (t : cvc5.Term) (bvs : Std.HashSet cvc5.Term) : Std.HashSet cvc5.Term := Id.run do
    if t.getKind == .VARIABLE then
      return bvs.insert t
    let mut bvs := bvs
    for ct in t do
      bvs := go ct bvs
    return bvs

partial def getFreeVars (t : cvc5.Term) : Std.HashSet cvc5.Term :=
  go t {}
where
  go (t : cvc5.Term) (fvs : Std.HashSet cvc5.Term) : Std.HashSet cvc5.Term := Id.run do
    if t.getKind == .CONSTANT then
      return fvs.insert t
    let mut bvs := fvs
    for ct in t do
      bvs := go ct bvs
    return bvs

partial def getUninterpretedSorts (t : cvc5.Term) : Std.HashSet cvc5.Sort :=
  let vs := getBoundVars t ∪ getFreeVars t
  vs.fold (fun ss v => go v.getSort ss) {}
where
  go (s : cvc5.Sort) (ss : Std.HashSet cvc5.Sort) : Std.HashSet cvc5.Sort := Id.run do
    if s.getKind == .UNINTERPRETED_SORT || s.getKind == .INTERNAL_SORT_KIND then
      return ss.insert s
    if s.getKind != .FUNCTION_SORT then
      return ss
    let mut ss := ss
    for ds in s.getFunctionDomainSorts! do
      ss := go ds ss
    ss := go s.getFunctionCodomainSort! ss
    return ss

def withDeclaredSorts [Inhabited α] (ss : Array cvc5.Sort) (k : Std.HashMap String FVarId → Array Expr → MetaM α) : MetaM α := do
  let sorts := ss.map (fun s => (Name.mkSimple s.getSymbol!, fun _ => return q(Type)))
  let mut insts := #[]
  for i in [:ss.size] do
    insts := insts.push (`inst, fun xs => return .app q(Nonempty.{1}) xs[i]!)
  Meta.withLocalDeclsD (sorts ++ insts) (fun xs => Id.run do
    let mut fvNames := {}
    for p in ss.zip xs do
      fvNames := fvNames.insert p.fst.getSymbol! p.snd.fvarId!
    k fvNames xs)

def withDeclaredFuns [Inhabited α] (vs : Array cvc5.Term) (fvNames : Std.HashMap String FVarId) (k : Std.HashMap String FVarId → Array Expr → MetaM α) : MetaM α := do
  let ctx := { userNames := fvNames, native := false }
  let state := ⟨{}, {}, 0, #[], #[]⟩
  let fvs : Array (Name × (Array Expr → MetaM Expr)) := vs.map fun v => (Name.mkSimple v.getSymbol!, fun _ => do
    let (t, _) ← (Smt.Reconstruct.reconstructSort v.getSort).run ctx state
    return t)
  Meta.withLocalDeclsD fvs (fun xs => Id.run do
    let mut fvNames := {}
    for p in vs.zip xs do
      fvNames := fvNames.insert p.fst.getSymbol! p.snd.fvarId!
    k fvNames xs)

def withDecls [Inhabited α] (ss : Array cvc5.Sort) (vs : Array cvc5.Term) (k : Std.HashMap String FVarId → Array Expr → MetaM α) : MetaM α := withTraceNode `withDecls trace do
  withDeclaredSorts ss fun fvNames₁ ts => withDeclaredFuns vs fvNames₁ fun fvNames₂ fvs =>
    k (fvNames₁.fold (·.insert) fvNames₂) (ts ++ fvs)

def checkProof (pf : cvc5.Proof) (native : Bool) : MetaM Unit := withTraceNode `checkProof trace do
  let t0 ← IO.monoMsNow
  withDecls (getUninterpretedSorts pf.getResult).toArray (getFreeVars pf.getResult).toArray fun fvNames xs => do
  let ctx := { userNames := fvNames, native := native }
  let (_, _, type, value, mvs) ← Smt.reconstructProof pf ctx
  if !mvs.isEmpty then
    IO.printlnAndFlush "[reconstruct] proof contains trusted steps"
    for mv in mvs do
      let p : Q(Prop) ← mv.getType
      mv.assign q(sorry : $p)
  let value ← instantiateMVars value
  let value ← Meta.mkLambdaFVars xs value
  let type ← Meta.mkForallFVars xs type
  let t1 ← IO.monoMsNow
  IO.printlnAndFlush s!"[time] reconstruct: {t1 - t0}"
  let r ← withTraceNode `kernel trace do
    return (← getEnv).toKernelEnv.addDecl (← getOptions) (.thmDecl { name := ← Lean.mkAuxName `thm 1, levelParams := [], type := type, value })
  match r with
  | .error e =>
    logError m!"Error: {e.toMessageData (← getOptions)}"
  | .ok env =>
    logInfo "ok"
  let t2 ← IO.monoMsNow
  IO.printlnAndFlush s!"[time] kernel: {t2 - t1}"

def solveAndCheck (query : String) (native : Bool) : MetaM Unit := withTraceNode `solveAndCheck trace do
  let t0 ← IO.monoMsNow
  let r ← solve query
  let t1 ← IO.monoMsNow
  IO.printlnAndFlush s!"[time] solve: {t1 - t0}"
  match r with
  | .error e =>
    logError (repr e)
  | .ok pf =>
    activateScoped `Classical
    checkProof pf native

def runSolveAndCheck (query : String) (native : Bool) : MetaM Unit := do
  solveAndCheck query native
  printTraces
  _ ← Language.reportMessages (← Core.getMessageLog) (← getOptions)

def elabSolveAndCheck (path : String) (native := false) : Elab.Command.CommandElabM Unit := do
  let query ← IO.FS.readFile path
  Elab.Command.runTermElabM fun _ => solveAndCheck query native

end Checker
