import Lean

open Lean Lean.Elab.Tactic

-- Attribute for point values
declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := autograded_proof) "autogradedProof" ptVal : attr
syntax (name := autograded_def) "autogradedDef" ptVal : attr
syntax:50 (name := valid_tactics) "validTactics" "#[" sepBy(tactic, ",") "]" : attr
syntax:50 (name := default_tactics) "defaultTactics" "#[" sepBy(tactic, ",") "]" : attr

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

initialize legalAxiomAttr : TagAttribute ←
  registerTagAttribute `legalAxiom
    "Marks an axiom as acceptable for use in autograded solutions"
