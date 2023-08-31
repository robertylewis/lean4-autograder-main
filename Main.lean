import Lean
import AutograderLib
-- import Mathlib -- ensures Mathlib is compiled when the container is being uploaded
open Lean IO System Elab Command

def agPathPrefix : FilePath := "lake-packages" / "autograder"
def solutionDirName := "AutograderTests"
def solutionModuleName := "Solution"

-- Used for non-exercise-specific results (e.g., global failures)
structure GradescopeResult where
  score : Float
  output : String
  deriving ToJson

structure ExerciseResult extends GradescopeResult where
  name : Name
  status : String
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

def validAxioms : Array Name :=
  #["Classical.choice".toName, "Quot.sound".toName, "propext".toName, "funext".toName] 

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

def getTemplateFromGitHub : IO Unit := do
  -- Read JSON config
  let configRaw ← IO.FS.readFile (agPathPrefix / "autograder_config.json")
  let config ← IO.ofExcept $ Json.parse configRaw
  let templateFile : FilePath := agPathPrefix / solutionDirName / s!"{solutionModuleName}.lean"
  if ← templateFile.pathExists then FS.removeFile templateFile
  let repoURLPath ← IO.ofExcept $ config.getObjValAs? String "public_repo"
  let some repoName := (repoURLPath.splitOn "/").getLast? 
    | throw <| IO.userError s!"Invalid public_repo found in autograder_config.json"
  
  -- Download the repo
  let repoLocalPath : FilePath := agPathPrefix / repoName
  let out ← IO.Process.output {
    cmd := "git"
    args := #["clone", s!"https://github.com/{repoURLPath}", repoLocalPath.toString]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"Failed to download public repo from GitHub"
  
  -- Move the assignment to the correct location; delete the cloned repo
  let assignmentPath ← IO.ofExcept $ config.getObjValAs? String "assignment_path"
  let curAsgnFilePath : FilePath := agPathPrefix / repoName / assignmentPath
  IO.FS.rename curAsgnFilePath templateFile
  IO.FS.removeDirAll repoLocalPath

-- Throw error and show it to the student
def exitWithError (errMsg : String) : IO Unit := do
  let resultsPath : FilePath := ".." / "results" / "results.json"
  let result : GradescopeResult := {output := errMsg, score := 0.0}
  IO.FS.writeFile resultsPath (toJson result).pretty
  throw <| IO.userError errMsg

def compileTests (submissionName : String) : IO Unit := do
  -- Check that the template compiles sans student submission
  let compileArgs : Process.SpawnArgs := {
    cmd := "/root/.elan/bin/lake"
    args := #["build", "autograder", solutionDirName]
  }
  let out ← IO.Process.output compileArgs
  if out.exitCode != 0 then
    exitWithError $
      "The autograder failed to compile itself. This is unexpected. Please let "
        ++ "your instructor know and provide a link to this Gradescope submission."
  
  -- Compile with the student submission
  let studentAsgnPath : FilePath := agPathPrefix / solutionDirName / submissionName
  IO.FS.writeFile studentAsgnPath (← IO.FS.readFile submissionName)
  let out ← IO.Process.output compileArgs
  if out.exitCode != 0 then
    exitWithError $
      "Your file failed to compile. There must be some red error messages "
        ++ "remaining in it. Fix these, and submit again!"

def main (args : List String) : IO Unit := do
  let usage := throw <| IO.userError s!"Usage: autograder submission-file.lean"
  let [submission] := args | usage
  getTemplateFromGitHub
  compileTests submission
  let submission : FilePath := submission
  let sheetName := s!"{solutionDirName}.{solutionModuleName}".toName
  searchPathRef.set (← addSearchPathFromEnv {})
  let sheet ← importModules [{module := sheetName}] {}
  let submissionBuildDir : FilePath := "build" / "submission"
  FS.createDirAll submissionBuildDir
  let submissionOlean := submissionBuildDir / "Submission.olean"
  if ← submissionOlean.pathExists then FS.removeFile submissionOlean
  let mut errors := #[]
  let submissionEnv ←
    try
      let out ← IO.Process.output {
        cmd := "lean"
        args := #[submission.toString, "-o", submissionOlean.toString]
      }
      if out.exitCode != 0 then
        let result : ExerciseResult := { name := toString submission, status := "failed", output := out.stderr , score := 0.0 }
        let results : GradingResults := { tests := #[result] }
        IO.FS.writeFile "../results/results.json" (toJson results).pretty
        throw <| IO.userError s!"Lean exited with code {out.exitCode}:\n{out.stderr}"
      searchPathRef.modify fun sp => submissionBuildDir :: sp
      -- Is `importModules` silently failing? If so, it might be because the
      -- autograder has not been allocated enough resources on Gradescope!
      importModules [{module := `Submission}] {}
    catch ex =>
      errors := errors.push ex.toString
      importModules sheet.header.imports.toList {}
  let tests ← gradeSubmission sheetName sheet submissionEnv
  let results : GradingResults := { tests }
  if errors.size == 0 then
    IO.FS.writeFile "../results/results.json" (toJson results).pretty
