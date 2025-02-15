/-
  **FILE** `LeanPlayground/Preso/Programming.lean`
  **PURPOSE** Introduction to programming programs
-/

-- .; TIMED AT 2025-02-15-17-45: Takes 09:11 to get through.
-- .; That's too long. Target is 7 mins.

import LeanPlayground.Preso.Res.Maybe
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
  fun n => [n, n]
  -- sorry
#reduce funny 6

-- We can simulate "multiple arguments" with the following pattern:
--  `: A → (B → C)`   (aka. `A → B → C`)
def hilarious : Nat → (Nat → Nat) :=
  fun x y => x + 2 * y
  -- sorry
#reduce hilarious 4 2



/- SECTION: Inductive Types -/

-- To do *interesting* computation, we build our own types.
-- For this, we have **inductive** types.

-- A cool example is the **`Maybe`** type:
-- *fine print: (Lean's standard library actually uses none, some & Option)*
inductive Maybe' (α : Type) where
  | nothing : Maybe' α
  | just : α → Maybe' α

/-- `divide? n d` returns `nothing` if `d = 0`. -/
def divide? : Nat → Nat → Maybe Nat :=
  fun n d =>
  if d = 0 then nothing else some (n / d)
  -- sorry

/-- `isNothing x?` returns `true` if `x? = nothing`. -/
def isNothing : Maybe Nat → Bool :=
  fun x? =>
  match x? with
  | nothing => true
  | just x => false
  -- sorry

-- Importantly, `inductive` types can be **recursive**:
inductive Nat' : Type where
  | zero : Nat'
  | succ : Nat' → Nat' -- *`succ n` represents `n + 1`*
#reduce (.succ (.succ .zero) : Nat)
