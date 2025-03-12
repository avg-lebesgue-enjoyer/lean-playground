/-
  **FILE** `LeanPlayground/Preso/Programming.lean`
  **PURPOSE** Introduction to programming programs
-/

/- IMPORTS: -/

import LeanPlayground.Preso.Res.«namespace-exports»
set_option pp.fieldNotation false
set_option linter.unusedVariables false
namespace a -- [hide:]










/- SECTION: Welcome to Lean :) -/










/- SECTION: Terms, Types and Functions -/

-- Everything in Lean is a **term**
example := 42
example := [0, 1, 2, 3]
example := Nat

section «types» -- [hide:]

-- All terms are categorised by **types**
#check 42
#check [0, 1, 2, 3]
#check Nat

end «types» -- [hide:]










-- *Computation* is about turning terms into other terms.
-- We do this using **functions**
def funny : Nat → List Nat :=
  sorry
#reduce funny 6

section «multiple arguments» -- [hide:]

-- We can simulate "multiple arguments" with the following pattern:
--  `: A → (B → C)`   (aka. `A → B → C`)
def hilarious : Nat → (Nat → Nat) :=
  sorry
#reduce hilarious 4 2

end «multiple arguments» -- [hide:]










/- SECTION: Inductive Types -/

-- To do *interesting* computation, we build our own types.
-- For this, we have **inductive** types.

section «`Nat`»

inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat' -- *`succ n` represents `n + 1`*
#reduce (zero : Nat)

section «`+`» -- [hide:]

/-- `add a b` computes the sum `a + b`. -/
def add : Nat → Nat → Nat :=
  sorry

end «`+`» end «`Nat`» -- [hide:]










/- SECTION: Shadow realm -/
section «shadow realm»

  -- A cool example is the **`Option α`** type:
  inductive Option' (α : Type) : Type where
    | none : Option' α
    | some : α → Option' α

  section «`divide?`»

    /-- `divide? n d` returns `none` if `d = 0`. -/
    def divide? : Nat → Nat → Option Nat :=
      fun n d =>
      if d = 0 then none else some (n / d)

    #reduce divide? 10 2

  end «`divide?`»

  section «`isNothing`»

    /-- `isNothing x?` returns `true` iff `x? = none`. -/
    def isNothing : Option Nat → Bool :=
      fun x? =>
      match x? with
      | none => true
      | some x => false
    #reduce isNothing (divide? 10 2)

  end «`isNothing`»

end «shadow realm»
