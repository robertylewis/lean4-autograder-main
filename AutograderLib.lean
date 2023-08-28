import Lean

open Lean

-- Attribute for point values
syntax (name := problem) scientific "points" : attr
initialize problemAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `problem
    descr := "specify a point value of a problem"
    -- applicationTime := .afterCompilation
    getParam := λ _ stx => match stx with
      | `(attr| $pts:scientific points) => 
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      | _  => throwError "invalid problem attribute"
    afterSet := λ _ _ => do pure ()
  }
