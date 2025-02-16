/-
  **FILE** `LeanPlayground/Preso/Proving.lean`
  **PURPOSE** Introduction to programming proofs
-/

-- .; 2025-02-16-03-26: yeah ~30:00. Needs major trimming. Target is 10:00

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
-- .; Target: +02:00

-- The simplest statements just use logic.
inductive True' : Prop where
  | intro : True' -- We have a canonical proof `intro : True`
inductive False' : Prop
  -- No proofs of `False'` can be constructed at all!

inductive Or' (p q : Prop) : Prop where
  | inl : p → Or' p q
  | inr : q → Or' p q

theorem Or.symm {p q : Prop}
  : p ∨ q → q ∨ p
  := sorry

-- NOTE: Implication `→`
#check Or.symm

set_option autoImplicit false -- *ignore this* [hide:]
-- NOTE: "For all" `∀`
theorem or_True : ∀ (p : Prop), p ∨ True :=
  fun p => inr True.intro
-- Decoding `∀`...
def  or_True' : Prop → p ∨ True
  := or_True
set_option autoImplicit true -- *ignore this* [hide:]
-- .; Target: +02:00

/- SECTION: Equality -/
-- ⚠: urgh, consider cutting this out... that feels so wrong though...

-- To form interesting proofs, we need **equality**.
-- `Eq` (or `=`) captures the fact that two terms are
-- *literally* the same.
-- *(fine print: "definitional" vs "propositional" equality)*
inductive Eq' {α : Type} : α → α → Prop where
  | refl : (a : α) → Eq' a a -- i.e. `∀a, a = a`

example : 6 = 6 := Eq.refl 6
example : 6 = 6 := rfl -- Lean can figure out the `6`
example : 1 + 2 + 3 = 6 := rfl -- Lean can *compute* `1 + 2 + 3` to `6`

-- *(I'm sorry, I just don't have more time to spend here ;^;)* [hide:]
-- .; Target: +01:30

/- SECTION: Interactive/automated theorem proving with `Nat` -/

def add : Nat → Nat → Nat :=
  fun x y => -- Compute `x + y`
    match y with
    | zero    => x                -- `x + 0 = x`
    | succ y' => succ (add x y')  -- `x + (succ y') = succ (x + y')`

theorem add_succ : ∀ (a b : Nat), a + succ b = succ (a + b)
  := sorry

-- GOAL: Prove that addition is *associative*:
--    `∀ (x y z : Nat), x + (y + z) = (x + y) + z`
--    Our proof is by induction on `z : Nat`.

-- Base case...
theorem add_assoc.base_case :
  ∀ (x y : Nat),
    x + (y + 0) = (x + y) + 0
  := sorry

-- Inductive step...
theorem add_assoc.inductive_step:
  ∀ (x y z : Nat),
    x + (y + z) = (x + y) + z -- inductive hypothesis
    → x + (y + succ z) = x + y + succ z
  := sorry -- `simp only`

theorem add_assoc
  : ∀ (x y z : Nat),
    x + (y + z) = (x + y) + z
  := sorry -- `match`, `apply`
section «notes on `add_assoc`»
  -- Two important things just happened:
  -- [1.] **induction is recursion.** (huge)
  -- [2.] `simp` **automates** finding arguments for the rules it's given
  -- Automation is a *convenience* and *practicality* thing.
  -- If you're curious, Lean can print out the full function that `simp`
  -- helped automate away:
  #print add_assoc.inductive_step
end «notes on `add_assoc`»
-- .; Target: +02:30

/- SECTION: `(as : List α) → (i : Nat) → (h : i < List.length as) → α` -/
end b -- *ignore this* [hide:]
namespace has_get -- *ignore this* [hide:]

#check get? -- *`: List α → Nat → Maybe α`*
#check get?_in_bounds -- *`: i < length as → get? as i ≠ nothing`*

def get : (as : List α) → (i : Nat) → i < length as → α :=
  sorry -- `match h_rep: ⋯`, `simp_all`

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
-- .; Target: +02:00

-- NOTE: Ending slides!!

/- SECTION: Other stuff if by some miracle I've got time -/
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
