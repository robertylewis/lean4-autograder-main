import Lean

open Lean

-- Attribute for point values
declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := problem) "autograded" ptVal : attr
syntax (name := problem_def) "autogradedDef" ptVal : attr

initialize problemAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `problem
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autograded $pts:num) => return pts.getNat.toFloat
      | `(attr| autograded $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid problem attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize definitionAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `problem_def
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autogradedDef $pts:num) => return pts.getNat.toFloat
      | `(attr| autogradedDef $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid problem attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize legalAxiomAttr : TagAttribute ←
  registerTagAttribute `legalAxiom
    "Marks an axiom as acceptable for use in autograded solutions"
