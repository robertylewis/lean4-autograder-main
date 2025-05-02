import Lean
import AutograderLib
-- Ensures Mathlib is compiled when the container is being uploaded:
-- import Mathlib
open Lean IO System Elab Command

-- Don't change these
def agPkgPathPrefix : FilePath := ".lake" / "packages" / "autograder"
def solutionDirName := "AutograderTests"
def submissionUploadDir : FilePath := "/autograder/submission"
def resultsJsonPath : FilePath := ".." / "results" / "results.json"
-- These are arbitrary
def solutionModuleName := "Solution"
def submissionFileName := "Assignment.lean"

-- These are generated based on the above
def sheetModuleName := s!"{solutionDirName}.{solutionModuleName}".toName
def sheetFileName := s!"{solutionModuleName}.lean"
def sheetFile : FilePath :=
  agPkgPathPrefix / solutionDirName / sheetFileName

-- Used for non-exercise-specific results (e.g., global failures)
structure FailureResult where
  output : String
  score : Float := 0.0
  output_format : String := "text"
  deriving ToJson

structure ExerciseResult where
  score : Float
  output : String
  name : Name
  status : String
  deriving ToJson

structure GradingResults where
  tests : Array ExerciseResult
  output: String
  output_format: String := "text"
  deriving ToJson

def Lean.Environment.moduleDataOf? (module : Name) (env : Environment)
  : Option ModuleData := do
  let modIdx : Nat ← env.getModuleIdx? module
  env.header.moduleData[modIdx]?

def Lean.Environment.moduleOfDecl? (decl : Name) (env : Environment)
  : Option Name := do
  let modIdx : Nat ← env.getModuleIdxFor? decl
  env.header.moduleNames[modIdx]?

def validAxioms : Array Name :=
  #["Classical.choice".toName,
    "Quot.sound".toName,
    "propext".toName,
    "funext".toName]

def axiomHasCorrectType (ax : Name) (sheet submission : Environment) : Bool :=
  match (sheet.find? ax, submission.find? ax) with
    | (some sheetConst, some subConst) => sheetConst.type == subConst.type
    | _                                => false

def findInvalidAxiom (submissionAxioms : List Name)
                     (sheet submission : Environment) : Option Name := do
  for ax in submissionAxioms do
    let isBaseAxiom := validAxioms.contains ax
    let isTaggedAxiom := legalAxiomAttr.hasTag sheet ax
    let isTypeCorrect := axiomHasCorrectType ax sheet submission

    -- If the axiom is not one of our predefined acceptable axioms, and is
    -- also not tagged in the stencil as legal, then it's invalid
    if ! (isBaseAxiom || isTaggedAxiom) || ! isTypeCorrect then
      return ax
  none

-- Ideally, we could format our Gradescope output nicely as HTML and escape
-- inserted file names/error messages/etc. Unfortunately, Gradescope doesn't
-- handle pre-escaped HTML well (it tries to re-escape it), so until a
-- workaround for that issue is found, we'll stick with plain text.
def escapeHtml (s : String) :=
  [("<", "&lt;"), (">", "&gt;"), ("&", "&amp;"), ("\"", "&quot;")].foldl
    (λ acc (char, repl) => acc.replace char repl) s

-- Throw error and show it to the student, optionally providing additional
-- information for the instructor only
def exitWithError {α} (errMsg : String) (instructorInfo: String := "")
  : IO α := do
  let result : FailureResult := {output := errMsg}
  IO.FS.writeFile resultsJsonPath (toJson result).pretty
  throw <| IO.userError (errMsg ++ "\n" ++ instructorInfo)

def gradeSubmission (sheet submission : Environment)
  : IO (Array ExerciseResult) := do
  let mut results := #[]

  for constEntry in sheet.constants.toList do
    let (name, constInfo) := constEntry
    -- Only consider annotated, non-internal declarations
    if let some pts := problemAttr.getParam? sheet name then
    if not name.isInternal then
      let result ←
        -- exercise to be filled in
        if let some subConstInfo := submission.find? name then
          -- Gather axioms in submitted declaration
          let (_, submissionState) :=
                ((CollectAxioms.collect name).run submission).run {}
          -- Tests:
          -- * Ensure declaration doesn't use `sorry` (separate from other
          --   axioms since it's especially common)
          if subConstInfo.value?.any (·.hasSorry) then
            pure { name,
                   status := "failed",
                   output := "Proof contains sorry",
                   score := 0.0 }
          -- * Ensure declaration type matches sheet
          else if not (constInfo.type == subConstInfo.type) then
              pure { name,
                     status := "failed",
                     output := "Type is different from expected: "
                                ++ s!"{constInfo.type} does not match "
                                ++ s!"{subConstInfo.type}",
                     score := 0.0 }
          -- * Submitted declaration must use only legal axioms
          else if let some badAx :=
            findInvalidAxiom submissionState.axioms.toList sheet submission
          then
            pure { name,
                    status := "failed",
                    output := s!"Uses unexpected axiom {badAx}",
                    score := 0.0 }
          -- * Submitted declaration must match the soundness of the sheet decl
          else if (subConstInfo.isUnsafe && ! constInfo.isUnsafe) ||
                  (subConstInfo.isPartial && ! constInfo.isPartial) then
            pure { name,
                    status := "failed",
                    output := "Declaration is partial or unsafe",
                    score := 0.0 }
          else
            pure { name,
                    status := "passed",
                    score := pts,
                    output := "Passed all tests" }
        else
          pure { name,
                 status := "failed",
                 output := "Declaration not found in submission",
                 score := 0.0 }
      results := results.push result

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    exitWithError <| "The autograder is unable to grade your submission "
        ++ "because no exercises have been marked as graded by your "
        ++ "instructor. Please notify your instructor of this error and "
        ++ "provide them with a link to this submission."
  return results

-- Returns a tuple of (fileName, outputMessage)
def moveFilesIntoPlace : IO (String × String) := do
  -- Copy the assignment's config file to the autograder directory
  -- IO.FS.writeFile (agPkgPathPrefix / "autograder_config.json")
  --     (← IO.FS.readFile "config.json")

  -- Copy the student's submission to the autograder directory. They should only
  -- have uploaded one Lean file; if they submitted more, we pick the first
  -- let submittedFiles ← submissionUploadDir.readDir
  -- let leanFiles := submittedFiles.filter
  --   (λ f => f.path.extension == some "lean")
  let leanFile : FS.DirEntry := {root := "./autograder", fileName := "Assignment.lean"} --leanFiles.get? (i := 0)
    -- | exitWithError <| "Your submission was not graded because it did not "
    --     ++ "contain a Lean file. Make sure to upload a single .lean file "
    --     ++ "containing your solutions."
  IO.FS.writeFile submissionFileName (← IO.FS.readFile leanFile.path)
  let output := ""
    -- if leanFiles.size > 1
    -- then "Warning: You submitted multiple Lean files. The autograder expects "
    --   ++ "you to submit a single Lean file containing your solutions, and it "
    --   ++ s!"will only grade a single file. It has picked {leanFile.fileName} "
    --   ++ "to grade; this may not be the file you intended to be graded.\n\n"
    -- else ""
  pure (leanFile.fileName, output)

def getTemplateFromGitHub : IO Unit := do
--   -- Read JSON config
--   let configRaw ← IO.FS.readFile (agPkgPathPrefix / "autograder_config.json")
--   let studentErrorText :=
--     "The autograder failed to run because it is incorrectly configured. Please "
--       ++ "notify your instructor of this error and provide them with a link to "
--       ++ "your submission."
--   let config ←
--     try
--       IO.ofExcept <| Json.parse configRaw
--     catch _ =>
--       exitWithError studentErrorText "Invalid JSON in autograder.json"
--   if ← sheetFile.pathExists then FS.removeFile sheetFile
--   let repoURLPath ← IO.ofExcept <| config.getObjValAs? String "public_repo"
--   let some repoName := (repoURLPath.splitOn "/").getLast?
--     | exitWithError studentErrorText "Invalid public_repo in autograder.json"

--   -- Download the repo
--   let repoLocalPath : FilePath := agPkgPathPrefix / repoName
--   let out ← IO.Process.output {
--     cmd := "git"
--     args := #["clone", s!"https://github.com/{repoURLPath}",
--               repoLocalPath.toString]
--   }
--   if out.exitCode != 0 then
--     exitWithError <|
--       "The autograder failed to run due to an issue retrieving the assignment. "
--         ++ "Try resubmitting in a few minutes. If the problem persists, "
--         ++ "contact your instructor and provide them with a link to this "
--         ++ "submission."

--   -- Move the assignment to the correct location; delete the cloned repo
--   let assignmentPath ← IO.ofExcept <|
--     config.getObjValAs? String "assignment_path"
  let curAsgnFilePath : FilePath := "." / "autograder" / "Solution.lean" --agPkgPathPrefix / repoName / assignmentPath
  IO.FS.rename curAsgnFilePath sheetFile
  -- IO.FS.removeDirAll repoLocalPath

def compileAutograder : IO Unit := do
  -- Compile the autograder so we get all our deps, even if the sheet itself
  -- fails to compile
  let compileArgs : Process.SpawnArgs := {
    cmd := "/root/.elan/bin/lake"
    args := #["build", "autograder", solutionDirName]
  }
  let out ← IO.Process.output compileArgs
  if out.exitCode != 0 then
    IO.println <| "WARNING: The autograder failed to compile. Note that this "
      ++ "may not be an error if your assignment template contains errors. "
      ++ "Compilation errors are printed below:\n"
      ++ out.stderr

def getErrorsStr (ml : MessageLog) : IO String := do
  let errorMsgs := ml.toList.filter (λ m => m.severity == .error)
  let errors ← errorMsgs.mapM (λ m => m.toString)
  let errorTxt := errors.foldl (λ acc e => acc ++ "\n" ++ e) ""
  return errorTxt

unsafe def main : IO Unit := do
  -- Get files into their appropriate locations
  let (studentFileName, output) ← moveFilesIntoPlace
  getTemplateFromGitHub
  -- We need to compile the AutograderTests directory to ensure that any
  -- libraries on which we depend get compiled (even if the sheet itself fails
  -- to compile)
  compileAutograder

  -- -- Import the template (as a module, since it is known to compile)
  -- let sheetName := s!"{solutionDirName}.{solutionModuleName}".toName
  -- searchPathRef.set (← addSearchPathFromEnv {})
  -- let sheet ← importModules [{module := sheetName}] {}

  -- Import the sheet (i.e., template/stencil)
  let sheetContents ← IO.FS.readFile sheetFile
  let sheetCtx := Parser.mkInputContext sheetContents sheetFileName
  let (sheetHeader, sheetParState, sheetMsgs) ← Parser.parseHeader sheetCtx

  enableInitializersExecution
  initSearchPath (← findSysroot)

  let (sheetHeadEnv, sheetMsgs)
    ← processHeader sheetHeader {} sheetMsgs sheetCtx

  if sheetMsgs.hasErrors then
    exitWithError (instructorInfo := (← getErrorsStr sheetMsgs)) <|
      "There was an error processing the assignment template's imports. This "
        ++ "error is unexpected. Please notify your instructor and provide a "
        ++ "link to your submission."

  let sheetCmdState : Command.State := Command.mkState sheetHeadEnv sheetMsgs {}
  let sheetFrontEndState
    ← IO.processCommands sheetCtx sheetParState sheetCmdState
  let sheet := sheetFrontEndState.commandState.env


  -- Grade the student submission
  -- Source: https://github.com/adamtopaz/lean_grader/blob/master/Main.lean
  let submissionContents ← IO.FS.readFile submissionFileName
  let inputCtx := Parser.mkInputContext submissionContents studentFileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  let (headerEnv, messages) ← processHeader header {} messages inputCtx

  if messages.hasErrors then
    exitWithError <|
      "Your Lean file could not be processed because its header contains "
      ++ "errors. This is likely because you are attempting to import a module "
      ++ "that does not exist. A log of these errors is provided below; please "
      ++ "correct them and resubmit:\n\n"
      ++ (← getErrorsStr messages)

  let cmdState : Command.State := Command.mkState headerEnv messages {}
  let frontEndState ← IO.processCommands inputCtx parserState cmdState
  let messages := frontEndState.commandState.messages
  let submissionEnv := frontEndState.commandState.env

  let err ← getErrorsStr messages
  let output := output ++
    if messages.hasErrors
    then "Warning: Your submission contains one or more errors, which are "
          ++ "listed below. You should attempt to correct these errors prior "
          ++ "to your final submission. Any responses with errors will be "
          ++ "treated by the autograder as containing \"sorry.\"\n"
          ++ err
    else ""

  -- Provide debug info for staff
  IO.println "Submission compilation output:"
  let os ← messages.toList.mapM (λ m => m.toString)
  IO.println <| os.foldl (·++·) ""

  let tests ← gradeSubmission sheet submissionEnv
  let results : GradingResults := { tests, output }
  IO.FS.writeFile resultsJsonPath (toJson results).pretty
