/-
  **FILE** `LeanPlayground/Preso/Programming.lean`
  **PURPOSE** Introduction to programming programs
-/

-- .; TIMED AT 2025-02-16-02-47: Takes 07:00 (target 07:00)

import LeanPlayground.Preso.Res.Maybe
import LeanPlayground.Preso.Res.«namespace-exports»
set_option pp.fieldNotation false
set_option linter.unusedVariables false
namespace a -- [hide:]

/- SECTION: Terms, Types and Functions -/
-- Everything in Lean is a **term**
example := 42
example := [0, 1, 2, 3]
example := Nat

-- All terms are categorised by **types**
-- *`#check` each of the things above*
#check 42
#check [0, 1, 2, 3]
#check Nat

-- *Computation* is about turning terms into other terms.
-- We do this using **functions**
def funny : Nat → List Nat :=
  sorry
#reduce funny 6

-- We can simulate "multiple arguments" with the following pattern:
--  `: A → (B → C)`   (aka. `A → B → C`)
def hilarious : Nat → (Nat → Nat) :=
  sorry
#reduce hilarious 4 2



/- SECTION: Inductive Types -/

-- To do *interesting* computation, we build our own types.
-- For this, we have **inductive** types.

-- A cool example is the **`Maybe`** type:
-- *fine print: (Lean's standard library actually uses none, some & Option)*
inductive Maybe' (α : Type) : Type where
  | nothing : Maybe' α
  | just : α → Maybe' α

/-- `divide? n d` returns `nothing` if `d = 0`. -/
def divide? : Nat → Nat → Maybe Nat :=
  sorry

/-- `isNothing x?` returns `true` if `x? = nothing`. -/
def isNothing : Maybe Nat → Bool :=
  sorry

-- Importantly, `inductive` types can be **recursive**:
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat' -- *`succ n` represents `n + 1`*
#reduce (succ (succ zero) : Nat)
