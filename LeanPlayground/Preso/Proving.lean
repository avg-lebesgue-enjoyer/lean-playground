/-
  **FILE** `LeanPlayground/Preso/Proving.lean`
  **PURPOSE** Introduction to programming proofs
-/

import LeanPlayground.Preso.Res.Maybe
import LeanPlayground.Preso.Res.get?
import LeanPlayground.Preso.Res.«namespace-exports»
set_option pp.fieldNotation false
set_option linter.unusedVariables false
namespace b -- [hide:]

/- SECTION: Logic -/

section «TODO: Move this into flashcards or 2nd monitor or smth»
  -- Mathematics is all about making logical **statements**
  -- and assembling their **proofs**.

  -- Just like `42` is some data satisfying `: Nat`,
  --      a `proof` is some data satisfying `: statement`.

  -- **`proof : statement`**
end «TODO: Move this into flashcards or 2nd monitor or smth»

-- The simplest statements just use logic.
inductive True' : Prop where
  | intro : True' -- We have a canonical proof `intro : True`
inductive False' : Prop
  -- No proofs of `False'` can be constructed at all!

inductive And' (p q : Prop) : Prop where
  | intro : p → q → And' p q

example : True ∧ True :=
  sorry

inductive Or' (p q : Prop) : Prop where
  | inl : p → Or' p q
  | inr : q → Or' p q

theorem Or.symm {p q : Prop}
  : p ∨ q → q ∨ p
  := sorry

-- NOTE: Implication `→`
#check Or.symm

-- ⚠: If anything needs to go, it's this
def Not' : Prop → Prop :=
  fun p => (p → False)

set_option autoImplicit false -- *ignore this* [hide:]
-- NOTE: "For all" `∀`
theorem or_True : ∀ (p : Prop), p ∨ True :=
  fun p => inr True.intro
-- Decoding `∀`...
def  or_True' : Prop → p ∨ True
  := or_True
set_option autoImplicit true -- *ignore this* [hide:]

/- SECTION: Equality -/

-- To form interesting proofs, we need **equality**.
-- `Eq` (or `=`) captures the fact that two terms are
-- *literally* the same.
-- *(fine print: "definitional" vs "propositional" equality)*
inductive Eq' {α : Type} : α → α → Prop where
  | refl : (a : α) → Eq' a a -- i.e. `∀a, a = a`

example : 6 = 6 := Eq.refl 6
example : 6 = 6 := rfl -- Lean can figure out the `6`
example : 1 + 2 + 3 = 6 := rfl -- Lean can *compute* `1 + 2 + 3` to `6`

-- An example of why `refl` is so magical:
theorem congrArg {α β : Type}
  (a₁ a₂ : α)
  (f : α → β)
  :   a₁ = a₂
  → f a₁ = f a₂
  := sorry

/- SECTION: Interactive/automated theorem proving with `Nat` -/

def add : Nat → Nat → Nat :=
  fun x y => -- Compute `x + y`
    match y with
    | zero    => x                -- `x + 0 = x`
    | succ y' => succ (add x y')  -- `x + (succ y') = succ (x + y')`

theorem add_zero : ∀ (a : Nat), a + 0 = a
  := sorry -- NOTE: `by`, `intro`, `rfl`
theorem add_succ : ∀ (a b : Nat), a + succ b = succ (a + b)
  := sorry

theorem add_assoc
  : ∀ (x y z : Nat),
    x + (y + z) = (x + y) + z
  := sorry -- NOTE: `match`, recursion/induction, `rw`
section «notes on `add_assoc`»
  -- Three important things just happened:
  -- [1.] **induction is recursion.** (huge)
  -- [2.] `rw` **automates** finding `congrArg`'s function.
  -- [3.] `rw` **automates** finding arguments for the rules it's given
  -- Automation is a *convenience* and *practicality* thing.
  -- If you're curious, Lean can print out the full function that `rw`
  -- helped automate away:
  #print add_assoc
end «notes on `add_assoc`»

-- This proof can be further optimised with `simp`
-- NOTE: `simp only` (not just `simp`)
theorem add_assoc'
  : ∀ (x y z : Nat),
    x + (y + z) = (x + y) + z
  := by
    intro x y z
    match z with
    | zero => rfl
    | succ z' =>
      simp only [add_succ, add_assoc']

/- SECTION: `(as : List α) → (i : Nat) → (h : i < List.length as) → α` -/

/-- `get? as n` retrieves the element of `as` at index `n`.
    If there is no such element, `nothing` gets returned.
    If there is such an element, `just` that element gets returned. -/
def get? : List α → Nat → Maybe α :=
  fun as i =>
  match as with
  | [] => nothing
  | (a :: as') =>
    match i with
    | .zero => just a
    | .succ i' => get? as' i'

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
#print get?_in_bounds -- lol

#check get? -- *`: List α → Nat → Maybe α`*
#check get?_in_bounds -- *`: i < length as → get? as i ≠ nothing`*

def get : (as : List α) → (i : Nat) → i < length as → α :=
  -- sorry -- `match h_rep: ⋯`, `simp_all`
  fun as i h =>
  match h_rep: get? as i with
  | just a => a
  | nothing => False.elim (by simp_all [get?_in_bounds])
section «notes on `get`»
  -- It is impossible to get an "index out of bounds error" using `get`,
  --  since using it requries providing a *proof* that the index is in
  --  bounds.

  -- In languages like Haskell and Java, an "index out of bounds" would
  --  **crash** the program.
  -- In languages like C, that could even be a **security vulnerability**.
  --  *(fine print: "buffer overflow", especially in user-given strings)*

  -- Aside from ensuring mathematical honesty, *formal verification can*
  --  *help us write safer code*.
end «notes on `get`»

/- SECTION: Other stuff if I've got time -/
section «other stuff»
  -- [1.] I proved the fundamental theorem of arithmetic in Lean... huge files...
  -- [2.] Lean's built-in automation is pretty small-scale. The current industry
  --      titan is `Isabelle/HOL`. Its whole *paradigm* is "get the automation to
  --      do stuff so that you don't have to".
  -- [3.] `Dafny` is a language that integrates correctness proofs (like what we
  --      did with `get : ⋯ → i < length as → ⋯`) into *imperative* programs.
  --      It's really cool; go check it out.
  -- [4.] Don't forget your ending slides lol -- FIXME: fuck I've gotta write those
end «other stuff»
