import Lean

open Lean

-- Attribute for point values
declare_syntax_cat ptVal
syntax num : ptVal
syntax scientific : ptVal
syntax (name := problem) ptVal "points" : attr

initialize problemAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `problem
    descr := "specify a point value of a problem"
    -- applicationTime := .afterCompilation
    getParam := λ _ stx => match stx with
      | `(attr| $pts:scientific points) => 
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | `(attr| $pts:num points) => return pts.getNat.toFloat
      | _  => throwError "invalid problem attribute"
    afterSet := λ _ _ => do pure ()
  }