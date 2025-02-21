/-
  **FILE** `LeanPlayground/Preso/Proving.lean`
  **PURPOSE** Introduction to programming proofs
-/

/- IMPORTS: -/

import LeanPlayground.Preso.Res.get?
import LeanPlayground.Preso.Res.«namespace-exports»
set_option pp.fieldNotation false
set_option linter.unusedVariables false
namespace b -- [hide:]










/- SECTION: Logic -/

section «the paradigm»

  -- Mathematics is all about making logical **statements**
  -- and assembling their **proofs**.

  -- Just like `42` is some data satisfying `: Nat`,
  --      a `proof` is some data satisfying `: statement`.

  -- **`proof : statement`**

end «the paradigm»









--                    **`proof : statement`**

-- The simplest statements just use logic.
inductive True' : Prop where
  | intro : True' -- We have a canonical proof `intro : True`
inductive False' : Prop
  -- No proofs of `False` can be constructed at all!










--                    **`proof : statement`**

inductive Or' (p q : Prop) : Prop where
  | inl : p → Or' p q
  | inr : q → Or' p q

section «Or.symm»

  theorem Or.symm {p q : Prop}
    : p ∨ q → q ∨ p
    := sorry

end «Or.symm»

section «→»

  #check Or.symm

end «→»










set_option autoImplicit false -- *ignore this* [hide:]
-- NOTE: "For all" `∀`
theorem or_True : ∀ (p : Prop), p ∨ True :=
  fun p => inr intro
-- Decoding `∀`...
def  or_True' : (p : Prop) → p ∨ True
  := or_True
set_option autoImplicit true -- *ignore this* [hide:]










/- SECTION: Interactive/automated theorem proving with `Nat` -/

/-- `add a b` computes the sum `a + b`. -/
def add : Nat → Nat → Nat :=
  fun a b => -- Compute `a + b`
    match b with
    | zero    => a                -- `a + 0 = a`
    | succ b' => succ (add a b')  -- `a + (succ b') = succ (a + b')`

section «`add_succ`»

  theorem add_succ : ∀ (a b : Nat), a + succ b = succ (a + b)
    := fun a b => rfl

end «`add_succ`»










-- GOAL: Prove that addition is *associative*:
--    `∀ (x y z : Nat), x + (y + z) = (x + y) + z`
--    Our proof is by induction on `z : Nat`.

section «base case»

  theorem base_case :
    ∀ (x y : Nat),
      x + (y + 0) = (x + y) + 0
    := sorry

end «base case»

section «inductive step»

  theorem inductive_step :
    ∀ (x y z : Nat),
      x + (y + z) = (x + y) + z -- inductive hypothesis
      → x + (y + succ z) = (x + y) + succ z
    := sorry -- `simp only`

end «inductive step»

section «`add_assoc`»

  #check base_case      -- *`x + (y + zero)    = (x + y) + zero   `*
  #check inductive_step -- *`x + (y + succ z') = (x + y) + succ z'`*
  --                       *`  ←  x + (y + z') = (x + y) + z'     `*
  theorem add_assoc
    : ∀ (x y z : Nat),
      x + (y + z) = (x + y) + z
    := sorry -- `match`, `apply`

end «`add_assoc`»

section «notes on `add_assoc`»

  -- Two important things just happened:
  -- [1.] **induction is recursion.** (huge)
  -- [2.] `simp` **automates** menial parts of proof.
  --      Automation is a *convenience* and *practicality* thing.

end «notes on `add_assoc`»










end b -- *ignore this* [hide:]
namespace has_get -- *ignore this* [hide:]
/- SECTION: `get` -/

#check get? -- *`: List α → Nat → Maybe α`*
#check get?_in_bounds -- *`: i < length as → get? as i ≠ nothing`*

def get : (as : List α) → (i : Nat) → i < length as → α :=
  sorry -- `match h_rep: ⋯`, `simp_all` -- *Time permitting*

section «notes on `get`»
/-
  It is impossible to get an "index out of bounds error" using`get`,
   since using it requries providing a *proof* that the index is in
   bounds.

  In languages like Haskell and Java, an "index out of bounds" would
   **crash** the program.
  In languages like C, that could even be a **security vulnerability**.
   *(fine print: "buffer overflow", especially in user-given strings)*

  Aside from ensuring mathematical honesty, *formal verification can*
   *help us write safer code*.

  NOTE: Ending slides!!
-/
end «notes on `get`»










/- SECTION: Other stuff if by some miracle I've got time -/
section «other stuff»
/-
  [0.] Equality (see below this section)

  [1.] I proved the fundamental theorem of arithmetic in Lean...
  --    huge files...

  [2.] Lean's built-in automation is pretty small-scale. The current
  --    industry titan is `Isabelle/HOL`. Its whole *paradigm* is "get
  --    the automation to do stuff so that you don't have to".

  [3.] `Dafny` is a language that integrates correctness proofs (like
  --    what we did with `get : ⋯ → i < length as → ⋯`) into
  --    *imperative* programs. It's really cool; go check it out.

  [4.] Don't forget your ending slides lol
-/
end «other stuff»










/- SECTION: Equality -/

-- To form interesting proofs, we need **equality**.
-- `Eq` (or `=`) captures the fact that two terms are
-- *literally* the same.
-- *(fine print: "definitional" vs "propositional" equality)*
inductive Eq' {α : Type} : α → α → Prop where
  | refl : (a : α) → Eq' a a -- i.e. `∀a, a = a`

-- NOTE: `Eq.refl`, `rfl`, computation

section «`congrArg`»
  -- Here's an example of `refl` being so magical:
  theorem congrArg :
    ∀ (α β : Type) (f : α → β) (a₁ a₂ : α),
          a₁ = a₂
      → f a₁ = f a₂
    := sorry
end «`congrArg`»
