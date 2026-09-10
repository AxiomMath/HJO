module

public meta import Lean

/-!
# The `hjo` tag attribute

A declaration attribute carrying a string tag, used to mark declarations.

    @[hjo "T001"]
    theorem my_result : True := trivial
-/

public meta section

open Lean

/-- `@[hjo "TAG"]` attaches the string tag `TAG` to a Lean declaration. -/
syntax (name := hjo) "hjo " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `hjo
  descr := "attaches a string tag to a declaration"
  add   := fun _ _ _ => pure ()
}

end
