/-
  **FILE** `LeanPlayground/Preso/Res/get?.lean`
  **PURPOSE**
    Provide the `get?` function and the `get?_in_bounds` lemma.
-/

/- IMPORTS: -/
import LeanPlayground.Preso.Res.«namespace-exports»

/- LAUNCH: `get?` -/
namespace has_get
  universe u
  variable {α : Type u}

  /--
    `get? as i` retrieves the element of `as` at index `i`.
    - If no such element exists, `none` is returned.
    - Otherwise, that element is returned (wrapped in `some`).
  ```
  #reduce get? [42, 1337] 0 -- *`some 42`*
  #reduce get? [42, 1337] 1 -- *`some 1337`*
  #reduce get? [42, 1337] 2 -- *`none`*
  ```
  -/
  def get? {α : Type} : List α → Nat → Option α :=
    fun as n =>
    match as with
    | [] => none
    | (a :: as') =>
      match n with
      | 0 => some a
      | .succ n' => get? as' n'

  theorem get?_in_bounds
    {α : Type}
    : ∀ {as : List α} {i : Nat},
        i < length as
        → get? as i ≠ none
    := by
      intro as
      induction as <;> simp_all
      intro i h
      simp [get?]
      split <;> simp_all
      -- [done.]
end has_get
