import Lean

open Lean

-- Attribute for point values
declare_syntax_cat ptVal
declare_syntax_cat ptWord
syntax num : ptVal
syntax scientific : ptVal
syntax "point" : ptWord
syntax "points" : ptWord
-- syntax (name := problem) ptVal ptWord : attr
syntax (name := problem) "autograded" ptVal : attr

initialize problemAttr : ParametricAttribute Float ←
  registerParametricAttribute {
    name := `problem
    descr := "Specifies the point value of a problem"
    getParam := λ _ stx => match stx with
      | `(attr| autograded $pts:num) => return pts.getNat.toFloat
      | `(attr| autograded $pts:scientific) =>
        let (n, s, d) := pts.getScientific
        return Float.ofScientific n s d
      -- | `(attr| $pts:scientific point) | `(attr| $pts:scientific points) => 
      --   let (n, s, d) := pts.getScientific
      --   return Float.ofScientific n s d
      -- | `(attr| $pts:num point) | `(attr| $pts:num points) =>
      --   return pts.getNat.toFloat
      | _  => throwError "Invalid problem attribute"
    afterSet := λ _ _ => do pure ()
  }
