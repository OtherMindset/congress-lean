-- Copied from OtherMindset/othermindset-lean-runner lean/ReportImports.lean at commit
-- 19af8de96ae5f5f4624b60f27106e9a292d68aa2, with the module prefix LongTable changed to LT2D (3 lines).
/-
  The runner's report for a file with imports (P4, the Long Table's handoff of 17 Nov 2026): the same two modes as
  Report.lean, for a Main that imports earlier posts built here as LongTable.P_<id>.

    axioms       as Report.lean, plus, for each theorem, the constants in its statement that an imported post's module
                 defines (imported_constants: name and module), so the site can show which post each comes from
    statements   as Report.lean, but the trusted environment for printing is the module's imports with every
                 LongTable.* module replaced by that module's own imports, transitively: core and Mathlib only. The
                 imported posts' notation, delaborators and initializers are never loaded, so they can't change what
                 is printed; their constants print by their full names (or the statement falls back to the raw term).

  Used only for jobs with imports, so a fault here can't touch other jobs. Report.lean is unchanged.
-/
import Lean
open Lean Meta

-- Theorems listed under the name they were written with (a private theorem's own name); generated ones
-- (_proof_1 and the like) are left out.
def shownName (n : Name) : Option Name :=
  let shown := (privateToUserName? n).getD n
  if shown.isInternal then none else some shown

def axiomsReport (modName : Name) : IO Json := do
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0)
  let some modIdx := env.getModuleIdx? modName
    | throw <| IO.userError s!"module {modName} not found"
  let data := env.header.moduleData[modIdx.toNat]!
  let ctx : Core.Context := { fileName := "<report>", fileMap := default, maxHeartbeats := 0 }
  let mut thms : Array Json := #[]
  let mut axs : Array Json := #[]
  for ci in data.constants do
    match ci with
    | .thmInfo t =>
      let some shown := shownName t.name | continue
      let (used, _) ← (collectAxioms t.name : CoreM (Array Name)).toIO ctx { env := env }
      let locals := t.type.getUsedConstants.filter fun c => env.getModuleIdxFor? c == some modIdx
      let mut imported : Array Json := #[]
      for c in t.type.getUsedConstants do
        match env.getModuleIdxFor? c with
        | some idx =>
          let m := env.header.moduleNames[idx.toNat]!
          if (`LT2D).isPrefixOf m then
            imported := imported.push <| Json.mkObj [("name", toJson c.toString), ("module", toJson m.toString)]
        | none => pure ()
      thms := thms.push <| Json.mkObj [("name", toJson shown.toString), ("axioms", toJson (used.map (·.toString))),
        ("local_constants", toJson (locals.map (·.toString))), ("imported_constants", Json.arr imported)]
    | .axiomInfo a => axs := axs.push (toJson a.name.toString)
    | _ => pure ()
  return Json.mkObj [("module", toJson modName.toString), ("theorems", Json.arr thms), ("declared_axioms", Json.arr axs)]

-- The imports to print with: every LT2D.* module is replaced by its own imports, transitively, read from its
-- .olean without loading it, so only core and Mathlib modules remain.
unsafe def trustedImports (imps : Array Import) : IO (Array Import) := do
  let mut out : Array Import := #[]
  let mut seen : NameSet := {}
  let mut todo := imps.toList
  repeat
    match todo with
    | [] => break
    | i :: rest =>
      todo := rest
      if seen.contains i.module then continue
      seen := seen.insert i.module
      if (`LT2D).isPrefixOf i.module then
        let (d, _) ← readModuleData (← findOLean i.module)
        todo := todo ++ d.imports.toList
      else
        out := out.push i
  return out

unsafe def statementsReport (modName : Name) : IO Json := do
  let file ← findOLean modName
  let (data, _region) ← readModuleData file
  -- The trusted environment for printing: the module's imports only, with their notation (their initializers are
  -- the toolchain's and Mathlib's own).
  enableInitializersExecution
  let penv ← importModules (← trustedImports data.imports) {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<report>", fileMap := default, maxHeartbeats := 0 }
  let mut out : Array Json := #[]
  for ci in data.constants do
    match ci with
    | .thmInfo t =>
      let some shown := shownName t.name | continue
      let act : CoreM String := (do let f ← ppExpr t.type; pure (toString f) : MetaM String).run'
      let s ← try
          let (s, _) ← act.toIO ctx { env := penv }
          pure s
        catch _ => pure (toString t.type)
      out := out.push <| Json.mkObj [("name", toJson shown.toString), ("statement", toJson s)]
    | _ => pure ()
  return Json.mkObj [("module", toJson modName.toString), ("statements", Json.arr out)]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | ["axioms", m] => IO.println (← axiomsReport m.toName).compress; return 0
  | ["statements", m] => IO.println (← statementsReport m.toName).compress; return 0
  | _ => IO.eprintln "usage: lean --run Report.lean (axioms|statements) <Module>"; return 2
