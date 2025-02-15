/-
  **FILE** `LeanPlayground/Preso/Res/get?.lean`
  **PURPOSE**
    Provide the `get?` function, in case I screw up writing it in the presentation.
-/

/- IMPORTS: -/
import LeanPlayground.Preso.Res.Maybe

/- LAUNCH: `get?` -/
namespace has_get
  universe u
  variable {α : Type u}

  def get? : List α → Nat → Maybe α :=
    fun as n =>
    match as with
    | [] => nothing
    | (a :: as') =>
      match n with
      | 0 => just a
      | .succ n' => get? as' n'
end has_get
