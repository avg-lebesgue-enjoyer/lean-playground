/-
  **FILE** `LeanPlayground/Preso/Res/get?.lean`
  **PURPOSE**
    Provide the `get?` function and the `get?_in_bounds` lemma.
-/

/- IMPORTS: -/
import LeanPlayground.Preso.Res.Maybe
import LeanPlayground.Preso.Res.«namespace-exports»

/- LAUNCH: `get?` -/
namespace has_get
  universe u
  variable {α : Type u}

  /-- `get? as i` retrieves the element of `as` at index `i`.
      - If no such element exists, `nothing` is returned.
      - Otherwise, `just` that element is returned.-/
  def get? : List α → Nat → Maybe α :=
    fun as n =>
    match as with
    | [] => nothing
    | (a :: as') =>
      match n with
      | 0 => just a
      | .succ n' => get? as' n'

  theorem get?_in_bounds
    : ∀ (as : List α) (i : Nat),
        i < length as
        → get? as i ≠ nothing
    := by
      intro as
      induction as <;> simp_all
      intro i h
      simp [get?]
      split <;> simp_all
      -- [done.]
end has_get
