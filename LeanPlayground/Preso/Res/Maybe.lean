/-
  **FILE** `LeanPlayground/Preso/Res/Maybe.lean`
  **PURPOSE**
    Provide the `Maybe` datatype, which is just a re-named `Option`.
    Out of sight and out of mind for the preso
-/

/- LAUNCH: -/
universe u
variable {α : Type u}

abbrev Maybe := Option
@[match_pattern] abbrev nothing : Option α := none
@[match_pattern] abbrev just : α → Option α := some
