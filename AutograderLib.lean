import Lean

open Lean Lean.Elab.Tactic

-- Main autograder attributes
declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := autograded_proof) "autogradedProof" ptVal : attr
syntax (name := autograded_def) "autogradedDef" ptVal : attr

initialize autogradedProofAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `autograded_proof
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autogradedProof $pts:num) => return pts.getNat.toFloat
      | `(attr| autogradedProof $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid autograded proof attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize autogradedDefAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `autograded_def
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autogradedDef $pts:num) => return pts.getNat.toFloat
      | `(attr| autogradedDef $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid autograded definition attribute"
    afterSet := λ _ _ => do pure ()
  }

-- Customize valid axioms
syntax:50 (name := valid_axioms) "validAxioms" "#[" sepBy(ident, ",") "]" : attr

initialize validAxiomsAttr : ParametricAttribute (Array Name) ←
  registerParametricAttribute {
    name := `valid_axioms
    descr := "Specifies the axioms allowed in a proof"
    getParam := λ _ stx =>
      match stx with
        | `(attr| validAxioms #[$axs,*]) =>
          return axs.getElems.map fun ax => (
          ax.raw.prettyPrint.pretty.toName)
        | _ => throwError "Invalid valid axiom attribute"
    afterSet := λ _ _ => do pure ()
  }


-- Autograder tactics attributes
syntax:50 (name := valid_tactics) "validTactics" "#[" sepBy(tactic, ",") "]" : attr
syntax:50 (name := default_tactics) "defaultTactics" "#[" sepBy(tactic, ",") "]" : attr

initialize validTacticsAttr : ParametricAttribute (Array (String × TacticM Unit)) ←
  registerParametricAttribute {
    name := `valid_tactics
    descr := "Specifies the tactics run to validate a solution"
    getParam := λ _ stx =>
      match stx with
        | `(attr| validTactics #[$tacs,*]) =>
          return tacs.getElems.map fun tac => (
            tac.raw.prettyPrint.pretty.trim,
            do evalTactic tac.raw)
        | _ => throwError "Invalid valid tactic attribute"
    afterSet := λ _ _ => do pure ()
  }


-- We expect this to be an attribute that is set up over the config definition
initialize defaultTacticsAttr : ParametricAttribute (Array (String × TacticM Unit)) ←
  registerParametricAttribute {
    name := `default_tactics
    descr := "Specifies the default tactics run to validate a solution"
    getParam := λ _ stx =>
      match stx with
        | `(attr| defaultTactics #[$tacs,*]) =>
          return tacs.getElems.map fun tac => (
            tac.raw.prettyPrint.pretty.trim,
            do evalTactic tac.raw)
        | _ => throwError "Invalid default tactic attribute"
    afterSet := λ _ _ => do pure ()
  }

-- Testing the autograder
declare_syntax_cat exerciseType
syntax "proof" : exerciseType
syntax "def" : exerciseType

declare_syntax_cat status
syntax "passes" : status
syntax "fails" : status

syntax (name := autograder_test) "autograderTest" status name : attr

initialize autograderTestAttr : ParametricAttribute (Name × String) ←
  registerParametricAttribute {
    name := `autograder_test
    descr := "For testing purposes, specifies whether a submission is expected to pass or fail a test"
    getParam := λ _ stx => match stx with
      | `(attr| autograderTest passes $n) => return (n.getName, "passed")
      | `(attr| autograderTest fails $n) => return (n.getName, "failed")
      | _ => throwError "Invalid test autograder attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize legalAxiomAttr : TagAttribute ←
  registerTagAttribute `legalAxiom
    "Marks an axiom as acceptable for use in autograded solutions"
