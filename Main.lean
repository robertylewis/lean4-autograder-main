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
      -- importModules [{module := `Submission}] {}
      importModules [] {}
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
