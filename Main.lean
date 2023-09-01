import Lean
import AutograderLib
-- import Mathlib -- ensures Mathlib is compiled when the container is being uploaded
open Lean IO System Elab Command

def agPkgPathPrefix : FilePath := "lake-packages" / "autograder"
def solutionDirName := "AutograderTests"
def solutionModuleName := "Solution"
def submissionFileName := "Assignment.lean"
def submissionUploadDir : FilePath := "/autograder/submission"

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
  outputFormat: String
  output: String
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

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    throw <| IO.userError <|
      "There are no exercises annotated with points in the template; thus, the "
        ++ "submission can't be graded."
  return results

-- Throw error and show it to the student
def exitWithError (errMsg : String) : IO Unit := do
  let resultsPath : FilePath := ".." / "results" / "results.json"
  let result : GradescopeResult := {output := errMsg, score := 0.0}
  IO.FS.writeFile resultsPath (toJson result).pretty
  throw <| IO.userError errMsg

-- TODO: should we warn if more than one Lean file submitted?
def moveFilesIntoPlace : IO Unit := do
  -- Copy the assignment's config file to the autograder directory
  IO.FS.writeFile (agPkgPathPrefix / "autograder_config.json")
      (← IO.FS.readFile "config.json")

  -- Copy the student's submission to the autograder directory. They should only
  -- have uploaded one Lean file; if they submitted more, we pick the first
  let submittedFiles ← submissionUploadDir.readDir
  let leanFile? := submittedFiles
    |> Array.filter (λ f => f.path.extension == some "lean")
    |> Array.get? (i := 0)
  if let some leanFile := leanFile? then
    IO.FS.writeFile submissionFileName (← IO.FS.readFile leanFile.path)
  else
    exitWithError <| "No Lean file was found in your submission. Make sure to "
        ++ "upload a single .lean file containing your solutions."
  

def getTemplateFromGitHub : IO Unit := do
  -- Read JSON config
  let configRaw ← IO.FS.readFile (agPkgPathPrefix / "autograder_config.json")
  let config ← IO.ofExcept $ Json.parse configRaw
  let templateFile : FilePath := agPkgPathPrefix / solutionDirName / s!"{solutionModuleName}.lean"
  if ← templateFile.pathExists then FS.removeFile templateFile
  let repoURLPath ← IO.ofExcept $ config.getObjValAs? String "public_repo"
  let some repoName := (repoURLPath.splitOn "/").getLast? 
    | throw <| IO.userError s!"Invalid public_repo found in autograder_config.json"
  
  -- Download the repo
  let repoLocalPath : FilePath := agPkgPathPrefix / repoName
  let out ← IO.Process.output {
    cmd := "git"
    args := #["clone", s!"https://github.com/{repoURLPath}", repoLocalPath.toString]
  }
  if out.exitCode != 0 then
    throw <| IO.userError s!"Failed to download public repo from GitHub"
  
  -- Move the assignment to the correct location; delete the cloned repo
  let assignmentPath ← IO.ofExcept $ config.getObjValAs? String "assignment_path"
  let curAsgnFilePath : FilePath := agPkgPathPrefix / repoName / assignmentPath
  IO.FS.rename curAsgnFilePath templateFile
  IO.FS.removeDirAll repoLocalPath

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
  -- let studentAsgnPath : FilePath := agPkgPathPrefix / solutionDirName / submissionName
  -- IO.FS.writeFile studentAsgnPath (← IO.FS.readFile submissionName)
  -- let out ← IO.Process.output compileArgs
  -- if out.exitCode != 0 then
  --   exitWithError $
  --     "Your file failed to compile. There must be some red error messages "
  --       ++ "remaining in it. Fix these, and submit again!"

def main : IO Unit := do
  -- Get files into their appropriate locations
  moveFilesIntoPlace
  getTemplateFromGitHub
  compileTests submissionFileName

  -- Grade
  let sheetName := s!"{solutionDirName}.{solutionModuleName}".toName
  searchPathRef.set (← addSearchPathFromEnv {})
  let sheet ← importModules [{module := sheetName}] {}

  -- let (submissionEnv, output) ← process (← IO.FS.readFile submissionFileName) (← mkEmptyEnvironment) {}
  
  -- Source: https://github.com/adamtopaz/lean_grader/blob/master/Main.lean
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile submissionFileName) "<input>"
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (headerEnv, messages) ← processHeader header {} messages inputCtx
  let cmdState : Command.State := Command.mkState headerEnv messages {}
  let frontEndState ← IO.processCommands inputCtx parserState cmdState
  let submissionEnv := frontEndState.commandState.env

  let errorMsgs := messages.msgs.filter (λ m => m.severity == .error)
  let errors ← errorMsgs.mapM (λ m => m.toString)
  let errorTxt := errors.foldl (λ acc e => e ++ "\n\n" ++ acc) ""
  let output :=
    if messages.hasErrors
    then "Your submission contains one or more errors, which are listed below. "
          ++ "You should attempt to correct these errors prior to your final "
          ++ "submission.\n\n"
          ++ errorTxt
    else ""
  
  -- Debug
  let os ← messages.toList.mapM (λ m => m.toString)
  IO.println os

  -- FIXME: not working
  -- let submissionBuildDir : FilePath := "build" / "submission"
  -- FS.createDirAll submissionBuildDir
  -- let submissionOlean := submissionBuildDir / "Submission.olean"
  -- if ← submissionOlean.pathExists then FS.removeFile submissionOlean
  -- let mut errors := #[]
  -- let submissionEnv ←
  --   try
  --     let out ← IO.Process.output {
  --       cmd := "lean"
  --       args := #[submissionFileName, "-o", submissionOlean.toString]
  --     }
  --     if out.exitCode != 0 then
  --       let result : ExerciseResult := {
  --           name := submissionFileName,
  --           status := "failed",
  --           output := out.stderr,
  --           score := 0.0
  --       }
  --       let results : GradingResults := { tests := #[result] }
  --       IO.FS.writeFile "../results/results.json" (toJson results).pretty
  --       throw <| IO.userError s!"Lean exited with code {out.exitCode}:\n{out.stderr}"
  --     searchPathRef.modify fun sp => submissionBuildDir :: sp
  --     -- Is `importModules` silently failing? If so, it might be because the
  --     -- autograder has not been allocated enough resources on Gradescope!
  --     -- TODO: look into replacing with `process`
  --     -- importModules [{module := `Submission}] {}
  --   catch ex =>
  --     errors := errors.push ex.toString
  --     importModules sheet.header.imports.toList {}
  let tests ← gradeSubmission sheetName sheet submissionEnv
  let results : GradingResults := { tests, output, outputFormat := "text" }
  IO.FS.writeFile "../results/results.json" (toJson results).pretty
  -- if errors.size == 0 then
  --   IO.FS.writeFile "../results/results.json" (toJson results).pretty
