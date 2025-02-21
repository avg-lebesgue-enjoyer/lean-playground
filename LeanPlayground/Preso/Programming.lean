/-
  **FILE** `LeanPlayground/Preso/Programming.lean`
  **PURPOSE** Introduction to programming programs
-/

/- IMPORTS: -/

import LeanPlayground.Preso.Res.«namespace-exports»
set_option pp.fieldNotation false
set_option linter.unusedVariables false
namespace a -- [hide:]










/- SECTION: Terms, Types and Functions -/

-- Everything in Lean is a **term**
example := 42
example := [0, 1, 2, 3]
example := Nat

section «types»

  -- All terms are categorised by **types**
  #check 42
  #check [0, 1, 2, 3]
  #check Nat

end «types»










-- *Computation* is about turning terms into other terms.
-- We do this using **functions**
def funny : Nat → List Nat :=
  sorry
#reduce funny 6

section «multiple arguments»

  -- We can simulate "multiple arguments" with the following pattern:
  --  `: A → (B → C)`   (aka. `A → B → C`)
  def hilarious : Nat → (Nat → Nat) :=
    sorry
  #reduce hilarious 4 2

end «multiple arguments»










/- SECTION: Inductive Types -/

-- To do *interesting* computation, we build our own types.
-- For this, we have **inductive** types.










-- A cool example is the **`Option α`** type:
inductive Option' (α : Type) : Type where
  | none : Option' α
  | some : α → Option' α

section «`divide?`»

  /-- `divide? n d` returns `none` if `d = 0`. -/
  def divide? : Nat → Nat → Option Nat :=
    sorry

  #reduce divide? 10 2

end «`divide?`»

section «`isNothing`» -- FIXME: consider removing, and introducing pattern matching only when needed

  /-- `isNothing x?` returns `true` if `x? = none`. -/
  def isNothing : Option Nat → Bool :=
    sorry
  #reduce isNothing (divide? 10 0)

end «`isNothing`»










-- Importantly, `inductive` types can be **recursive**:
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat' -- *`succ n` represents `n + 1`*
#reduce (zero : Nat)
