import Lean

open Lean Lean.Elab.Tactic

-- Attribute for point values
declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal

syntax (name := problem) "autograded" ptVal : attr
syntax (name := definition) "autogradedDef" ptVal : attr
syntax (name := validTactics) "validTactics" "#[" sepBy(tactic, ",") "]" : attr

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
    name := `definition
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autogradedDef $pts:num) => return pts.getNat.toFloat
      | `(attr| autogradedDef $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "Invalid problem attribute"
    afterSet := λ _ _ => do pure ()
  }

initialize tacticAttr : ParametricAttribute (Array (TacticM Unit)) ← 
  registerParametricAttribute {
    name := `validTactics
    descr := "Specifies the tactics run to validate a solution"
    getParam := λ _ stx => 
      match stx with
        | `(attr| validTactics #[$tacs,*]) =>
          return tacs.getElems.map fun tac => do evalTactic tac.raw
        | _ => throwError "Invalid tactic attribute"
    afterSet := λ _ _ => do pure ()
  }

def defaultTactics : Option (Array (TacticM Unit)):= do
  let mut res := #[]
  for tac in #[`(tactic| rfl), `(tactic| simp)] do
    let tacM : TacticM Unit := do evalTactic (← tac)
    res := res.push tacM
  return res 

initialize legalAxiomAttr : TagAttribute ←
  registerTagAttribute `legalAxiom
    "Marks an axiom as acceptable for use in autograded solutions"
