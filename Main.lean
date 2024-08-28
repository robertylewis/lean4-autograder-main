import Lean
import AutograderLib
-- Ensures Mathlib is compiled when the container is being uploaded:
-- import Mathlib
open Lean IO System Elab Command Meta Lean.Meta Lean.Elab.Tactic

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
-- ".lake/packages/autograder/AutograderTests/AutograderTests.Solution.lean"
def sheetFile : FilePath := agPkgPathPrefix / solutionDirName / sheetFileName

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

-- Source: aesop/Aesop/Util/Basic.lean
def runTacticMAsMetaM {α : Type} (tactic : TacticM α) (goals : List MVarId) :
    MetaM (α × List MVarId) := do
  let (a, s) ← tactic |>.run { elaborator := .anonymous } |>.run { goals } |>.run'
  return (a, s.goals)

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

def checkDefinition (name : Name) (pts : Float) (constInfo subConstInfo : ConstantInfo)
  (sheet : Environment) : IO ExerciseResult := do
    -- Get the list of tactics for the problem
    let tactics :=
      if let some t := validTacticsAttr.getParam? sheet name then t
      else if let some d := defaultTacticsAttr.getParam? sheet `setDefaultTactics then d
      else #[]

    -- * Ensure declaration doesn't use `sorry`
    if subConstInfo.value?.any (·.hasSorry) then
      pure { name,
             status := "failed",
             output := "Definition contains sorry",
             score := 0.0 }
    -- * Ensure declaration type matches sheet
    else if not (constInfo.type == subConstInfo.type) then
        pure { name,
               status := "failed",
               output := "Type is different from expected: "
                          ++ s!"{constInfo.type} does not match "
                          ++ s!"{subConstInfo.type}",
               score := 0.0 }
    -- * Submitted declaration must match the soundness of the sheet decl
    else if (subConstInfo.isUnsafe && ! constInfo.isUnsafe) ||
            (subConstInfo.isPartial && ! constInfo.isPartial) then
      pure { name,
              status := "failed",
              output := "Declaration is partial or unsafe",
              score := 0.0 }
    else if (!subConstInfo.hasValue) then
      pure { name,
             status := "failed",
             score := 0.0,
             output := "Definition does not contain a value" }
    else if (subConstInfo.value!.equal constInfo.value!) then
      pure { name,
             status := "passed",
             score := pts,
             output := "Marked as equal" }
    else if (subConstInfo.value!.eqv constInfo.value!) then
      pure { name,
             status := "passed",
             score := pts,
             output := "Marked as equivalent" }
    else
      let sheetExpr := constInfo.value!
      let subExpr := subConstInfo.value!

      -- Run tactics to prove equality
      let checkEquality : MetaM ExerciseResult := do
        -- Create a goal to prove that the two expressions are equal
        let eqExpr ← mkEq sheetExpr subExpr
        let mvar ← mkFreshExprMVar (some eqExpr)
        let mvarId := mvar.mvarId!

        -- Try refl and hrefl
        try mvarId.refl;
            return { name,
                     status := "passed",
                     output := "Proven to be equivalent by refl",
                     score := pts }
        catch _ => pure ()

        try mvarId.hrefl;
            return { name,
                     status := "passed",
                     output := "Proven to be equivalent by hrefl",
                     score := pts }
        catch _ => pure ()

        -- Run tactics to prove equality
        -- TODO: check if there is backtracking after the tactic is applied
        for (tacName, tac) in tactics do
          let (_, goals) ← runTacticMAsMetaM (try tac catch _ => pure ()) [mvarId]
          if goals.isEmpty then
            return { name,
                     status := "passed",
                     output := s!"Proven to be equivalent by {tacName}",
                     score := pts }

        return { name,
                 status := "failed",
                 score := 0.0,
                 output := "Not marked as equivalent" }

      let ctx : Core.Context := { fileName := "", fileMap := default }
      let cstate : Core.State := { env := sheet }
      let (proved?, _, _ ) ← MetaM.toIO checkEquality ctx cstate
      return proved?

def checkProof (name : Name) (pts : Float) (constInfo subConstInfo : ConstantInfo)
  (sheet submission : Environment) : IO ExerciseResult := do
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

def gradeSubmission (sheet submission : Environment) : IO (Array ExerciseResult) := do
  let mut results := #[]

  for (name, constInfo) in sheet.constants.toList do
    -- Autograde proofs
    if let some pts := autogradedProofAttr.getParam? sheet name then
        if not name.isInternal then
          if let some subConstInfo := submission.find? name then
              let result ← checkProof name pts constInfo subConstInfo sheet submission
              results := results.push result
            else
              let result :=
                { name,
                  status := "failed",
                  output := "Declaration not found in submission",
                  score := 0.0 }
              results := results.push result

    -- Autograde definitions
    else if let some pts := autogradedDefAttr.getParam? sheet name then
      if not name.isInternal then
        if let some subConstInfo := submission.find? name then
          let result ← checkDefinition name pts constInfo subConstInfo sheet
          results := results.push result
        else
          let result :=
            { name,
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

def testGradeSubmission (sheet submission : Environment) : IO (Array ExerciseResult) := do
  let mut results := #[]
  for (name, constInfo) in sheet.constants.toList do
    -- Check autograding of proofs
    if let some pts := autogradedProofAttr.getParam? sheet name then
      if not name.isInternal then
        let mut currResults := #[]
        -- Check every submission constant that is labeled as a test for the current sheet constant
        for (subName, subConstInfo) in submission.constants.toList do
          if let some (sheetName, expectedStatus) := autograderTestAttr.getParam? submission subName then
            if name == sheetName then
              let result ← checkProof subName pts constInfo subConstInfo sheet submission
              if result.status == expectedStatus then
                println! s!"Passed {subName}!"
              else
                println! s!"Passed {subName}!"
              currResults := currResults.push result
        results := results ++ currResults

    -- Check autograding of definitions
    else if let some pts := autogradedDefAttr.getParam? sheet name then
      if not name.isInternal then
        let mut currResults := #[]
        -- Check every submission constant that is labeled as a test for the current sheet constant
        for (subName, subConstInfo) in submission.constants.toList do
          if let some (sheetName, expectedStatus) := autograderTestAttr.getParam? submission subName then
            if name == sheetName then
              let result ← checkDefinition subName pts constInfo subConstInfo sheet
              if result.status == expectedStatus then
                println! s!"Passed {subName}!"
              else
                println! s!"Passed {subName}!"
              currResults := currResults.push result
        results := results ++ currResults

  -- Gradescope will not accept an empty tests list, and this most likely
  -- indicates a misconfiguration anyway
  if results.size == 0 then
    exitWithError <| "The autograder is unable to grade your submission "
        ++ "because no exercises have been marked as graded by your "
        ++ "instructor. Please notify your instructor of this error and "
        ++ "provide them with a link to this submission."

  return results

-- Returns a tuple of (fileName, outputMessage)
def moveFilesIntoPlace (localSubmission : Option String) : IO (String × String) := do
  -- Copy the assignment's config file to the autograder directory
  -- IO.FS.writeFile (agPkgPathPrefix / "autograder_config.json")
  --     (← IO.FS.readFile "config.json")


  match localSubmission with
  | none =>
    -- Copy the student's submission to the autograder directory. They should only
    -- have uploaded one Lean file; if they submitted more, we pick the first
    let submittedFiles ← submissionUploadDir.readDir
    let leanFiles := submittedFiles.filter
      (λ f => f.path.extension == some "lean")
    let some leanFile := leanFiles.get? (i := 0)
      | exitWithError <| "Your submission was not graded because it did not "
          ++ "contain a Lean file. Make sure to upload a single .lean file "
          ++ "containing your solutions."
    IO.FS.writeFile submissionFileName (← IO.FS.readFile leanFile.path)
    let output :=
      if leanFiles.size > 1
      then "Warning: You submitted multiple Lean files. The autograder expects "
        ++ "you to submit a single Lean file containing your solutions, and it "
        ++ s!"will only grade a single file. It has picked {leanFile.fileName} "
        ++ "to grade; this may not be the file you intended to be graded.\n\n"
      else ""
    pure (leanFile.fileName, output)
  | some path =>
    IO.FS.writeFile submissionFileName (← IO.FS.readFile path)
    pure (path, "")

def moveTemplateIntoPlace (localTemplate : Option String) : IO Unit := do
  let assignmentPath ←
    match localTemplate with
    | none =>
      let configRaw ← IO.FS.readFile "config.json"
      let studentErrorText :=
        "The autograder failed to run because it is incorrectly configured. Please "
          ++ "notify your instructor of this error and provide them with a link to "
          ++ "your submission."
      let config ←
        try
          IO.ofExcept <| Json.parse configRaw
        catch _ =>
          exitWithError studentErrorText "Invalid JSON in autograder.json"
      if ← sheetFile.pathExists then FS.removeFile sheetFile
      IO.ofExcept <| config.getObjValAs? String "assignment_path"

    | some path => pure path
  IO.FS.writeFile sheetFile (← IO.FS.readFile assignmentPath)

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

structure ConfigData where
  test            : Bool
  localRun        : Bool
  localSubmission : Option String
  localTemplate   : Option String
  deriving Repr

def parseArgsAux : ConfigData → List String → IO ConfigData
| cd, [] => pure cd
| cd, "--test"::rest => parseArgsAux { cd with test := true } rest
| cd, "--local"::submission::template::rest => parseArgsAux { cd with localRun := true, localSubmission := some submission, localTemplate := some template } rest
| _, s => exitWithError s!"Unknown argument: {s}"

def parseArgs : List String → IO ConfigData :=
  parseArgsAux ⟨false, false, none, none⟩

unsafe def main (args : List String) : IO Unit := do
  let cfg ← parseArgs args
  -- Check flags and set the grading function

  let gradeFunction :=
    if cfg.test then testGradeSubmission else gradeSubmission

  -- Get files into their appropriate locations
  let (studentFileName, output) ← moveFilesIntoPlace cfg.localSubmission
  moveTemplateIntoPlace cfg.localTemplate
  -- We need to compile the AutograderTests directory to ensure that any
  -- libraries on which we depend get compiled (even if the sheet itself fails
  -- to compile)

  if !cfg.localRun then compileAutograder

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

  let tests ← gradeFunction sheet submissionEnv

  -- TODO: if `cfg.localRun` is true, print these results instead of saving to json

  let results : GradingResults := { tests, output }
  IO.FS.writeFile resultsJsonPath (toJson results).pretty
