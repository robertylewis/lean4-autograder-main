import Lean
import AutograderLib
-- import Mathlib -- ensures Mathlib is compiled when the container is being uploaded
open Lean IO System Elab Command

structure ExerciseResult where
  score : Float
  name : Name
  status : String
  output : String
  deriving ToJson

structure GradingResults where
  tests : Array ExerciseResult
  deriving ToJson

def Lean.Environment.moduleDataOf? (module : Name) (env : Environment) : Option ModuleData := do
  let modIdx : Nat ← env.getModuleIdx? module
  env.header.moduleData[modIdx]?

def Lean.Environment.moduleOfDecl? (decl : Name) (env : Environment) : Option Name := do
  let modIdx : Nat ← env.getModuleIdxFor? decl
  env.header.moduleNames[modIdx]?

-- TODO: why isn't `funext` valid?
def validAxioms : Array Name := #["Classical.choice".toName, "Quot.sound".toName, "propext".toName] 

def usedAxiomsAreValid (submissionAxioms : List Name) : Bool := 
  match submissionAxioms with 
  | [] => true
  | x :: xs => if validAxioms.contains x then usedAxiomsAreValid xs else false

def gradeSubmission (sheetName : Name) (sheet submission : Environment) : IO (Array ExerciseResult) := do
  let some sheetMod := sheet.moduleDataOf? sheetName
    | throw <| IO.userError s!"module name {sheetName} not found"
  let mut results := #[]

  for name in sheetMod.constNames, constInfo in sheetMod.constants do
    -- Only consider annotated, non-internal declarations
    if let some pts := problemAttr.getParam? sheet name then
    if not name.isInternal then
      let result ←
        -- exercise to be filled in
        if let some subConstInfo := submission.find? name then
          if subConstInfo.value?.any (·.hasSorry) then
            pure { name, status := "failed", output := "Proof contains sorry", score := 0.0 }
          else
            if not (constInfo.type == subConstInfo.type) then
              pure { name, status := "failed", output := "Type is different than expected", score := 0.0 }
            else
              let (_, submissionState) := ((CollectAxioms.collect name).run submission).run {}
              if usedAxiomsAreValid submissionState.axioms.toList 
                then pure { name, status := "passed", score := pts, output := "Passed all tests" }
              else 
                pure { name, status := "failed", output := "Contains unexpected axioms", score := 0.0 }
        else
          pure { name, status := "failed", output := "Declaration not found in submission", score := 0.0 }
      results := results.push result

  -- TODO: do we actually need this?
  if results.size == 0 then  
    throw <| IO.userError "There are no exercises annotated with points in the template; thus, the submission can't be graded."
  return results

private def mkInitialExtensionStates : IO (Array EnvExtensionState) := EnvExtensionInterfaceImp.mkInitialExtStates

private def mkExtNameMap (startingAt : Nat) : IO (HashMap Name Nat) := do
  let descrs ← persistentEnvExtensionsRef.get
  let mut result := {}
  for h : i in [startingAt : descrs.size] do
    have : i < descrs.size := h.upper
    let descr := descrs[i]
    result := result.insert descr.name i
  return result


private def setImportedEntries (env : Environment) (mods : Array ModuleData) (startingAt : Nat := 0) : IO Environment := do
  let mut env := env
  let extDescrs ← persistentEnvExtensionsRef.get
  /- For extensions starting at `startingAt`, ensure their `importedEntries` array have size `mods.size`. -/
  for extDescr in extDescrs[startingAt:] do
    env := extDescr.toEnvExtension.modifyState env fun s => { s with importedEntries := mkArray mods.size #[] }
  /- For each module `mod`, and `mod.entries`, if the extension name is one of the extensions after `startingAt`, set `entries` -/
  let extNameIdx ← mkExtNameMap startingAt
  for h : modIdx in [:mods.size] do
    have : modIdx < mods.size := h.upper
    let mod := mods[modIdx]
    for (extName, entries) in mod.entries do
      if let some entryIdx := extNameIdx.find? extName then
        env := extDescrs[entryIdx]!.toEnvExtension.modifyState env fun s => { s with importedEntries := s.importedEntries.set! modIdx entries }
  return env

private def ensureExtensionsArraySize (env : Environment) : IO Environment :=
  EnvExtensionInterfaceImp.ensureExtensionsSize env

private partial def finalizePersistentExtensions (env : Environment) (mods : Array ModuleData) (opts : Options) : IO Environment := do
  loop 0 env
where
  loop (i : Nat) (env : Environment) : IO Environment := do
    -- Recall that the size of the array stored `persistentEnvExtensionRef` may increase when we import user-defined environment extensions.
    let pExtDescrs ← persistentEnvExtensionsRef.get
    if i < pExtDescrs.size then
      let extDescr := pExtDescrs[i]!
      let s := extDescr.toEnvExtension.getState env
      let prevSize := (← persistentEnvExtensionsRef.get).size
      let prevAttrSize ← getNumBuiltinAttributes
      let newState ← extDescr.addImportedFn s.importedEntries { env := env, opts := opts }
      let mut env := extDescr.toEnvExtension.setState env { s with state := newState }
      env ← ensureExtensionsArraySize env
      if (← persistentEnvExtensionsRef.get).size > prevSize || (← getNumBuiltinAttributes) > prevAttrSize then
        -- This branch is executed when `pExtDescrs[i]` is the extension associated with the `init` attribute, and
        -- a user-defined persistent extension is imported.
        -- Thus, we invoke `setImportedEntries` to update the array `importedEntries` with the entries for the new extensions.
        env ← setImportedEntries env mods prevSize
        -- See comment at `updateEnvAttributesRef`
        env ← updateEnvAttributes env
      loop (i + 1) env
    else
      return env

partial def myImportModules (imports : List Import) (opts : Options) (trustLevel : UInt32 := 0) : IO Environment := profileitIO "import" opts do
  for imp in imports do
    if imp.module matches .anonymous then
      throw <| IO.userError "import failed, trying to import module with anonymous name"
  withImporting do
    let (_, s) ← importMods imports |>.run {}
    let mut numConsts := 0
    for mod in s.moduleData do
      numConsts := numConsts + mod.constants.size + mod.extraConstNames.size
    let mut modIdx : Nat := 0
    let mut const2ModIdx : HashMap Name ModuleIdx := mkHashMap (capacity := numConsts)
    let mut constantMap : HashMap Name ConstantInfo := mkHashMap (capacity := numConsts)
    for mod in s.moduleData do
      for cname in mod.constNames, cinfo in mod.constants do
        match constantMap.insert' cname cinfo with
        | (constantMap', replaced) =>
          constantMap := constantMap'
          if replaced then
            throwAlreadyImported s const2ModIdx modIdx cname
        const2ModIdx := const2ModIdx.insert cname modIdx
      for cname in mod.extraConstNames do
        const2ModIdx := const2ModIdx.insert cname modIdx
      modIdx := modIdx + 1
    let constants : ConstMap := SMap.fromHashMap constantMap false
    let exts ← mkInitialExtensionStates
    IO.println "make initial states"
    let env : Environment := {
      const2ModIdx    := const2ModIdx
      constants       := constants
      extraConstNames := {}
      extensions      := exts
      header          := {
        quotInit     := !imports.isEmpty -- We assume `core.lean` initializes quotient module
        trustLevel   := trustLevel
        imports      := imports.toArray
        regions      := s.regions
        moduleNames  := s.moduleNames
        moduleData   := s.moduleData
      }
    }
    let env ← setImportedEntries env s.moduleData
    IO.println "set imported entries"
    let env ← finalizePersistentExtensions env s.moduleData opts
    IO.println "finalize persistent"
    pure env
where
  importMods : List Import → StateRefT ImportState IO Unit
  | []    => pure ()
  | i::is => do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      importMods is
    else do
      modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
      let mFile ← findOLean i.module
      unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
      let (mod, region) ← readModuleData mFile
      importMods mod.imports.toList
      modify fun s => { s with
        moduleData  := s.moduleData.push mod
        regions     := s.regions.push region
        moduleNames := s.moduleNames.push i.module
      }
      importMods is

def main (args : List String) : IO Unit := do
  let usage := throw <| IO.userError s!"Usage: autograder Exercise.Sheet.Module submission-file.lean"
  let [sheetName, submission] := args | usage
  let submission : FilePath := submission
  let some sheetName := Syntax.decodeNameLit ("`" ++ sheetName) | usage
  searchPathRef.set (← addSearchPathFromEnv {})
  let sheet ← importModules [{module := sheetName}] {}
  let submissionBuildDir : FilePath := "build" / "submission"
  FS.createDirAll submissionBuildDir
  IO.println "Initialized"
  let submissionOlean := submissionBuildDir / "Submission.olean"
  if ← submissionOlean.pathExists then FS.removeFile submissionOlean
  IO.println "Removed existing olean"
  let mut errors := #[]
  let submissionEnv ←
    try
      IO.println "Preparing to compile"
      let out ← IO.Process.output {
        cmd := "lean"
        args := #[submission.toString, "-o", submissionOlean.toString]
      }
      IO.println "Compilation complete"
      IO.println s!"Out: {out.stdout}"
      IO.println s!"Err: {out.stderr}"
      if out.exitCode != 0 then
        IO.println s!"Failed with nonzero exit code {out.exitCode}"
        let result : ExerciseResult := { name := toString submission, status := "failed", output := out.stderr , score := 0.0 }
        let results : GradingResults := { tests := #[result] }
        IO.FS.writeFile "../results/results.json" (toJson results).pretty
        throw <| IO.userError s!"Lean exited with code {out.exitCode}:\n{out.stderr}"
      IO.println "Compilation succeedded"
      searchPathRef.modify fun sp => submissionBuildDir :: sp
      IO.println "Modified search path"
      -- FIXME: silently crashing on `importModules`
      myImportModules [{module := `Submission}] {}
    catch ex =>
      IO.println "Unexpected error encountered; pushing to errors..."
      errors := errors.push ex.toString
      importModules sheet.header.imports.toList {}
  IO.println "Preparing to grade"
  let tests ← gradeSubmission sheetName sheet submissionEnv
  IO.println s!"Graded with results {tests.map (λ e => e.status)}"
  let results : GradingResults := { tests }
  if errors.size == 0 then
    IO.println "No errors; writing file"
    IO.FS.writeFile "../results/results.json" (toJson results).pretty
  -- For debugging
  else
    IO.println "Errors found; entering debug branch"
    let result : ExerciseResult := { name := toString submission, status := "failed", output := errors.foldl (λ e acc => e ++ "\n\n" ++ acc) "", score := 0.0 }
    let results : GradingResults := { tests := #[result] }
    IO.FS.writeFile "../results/results.json" (toJson results).pretty
