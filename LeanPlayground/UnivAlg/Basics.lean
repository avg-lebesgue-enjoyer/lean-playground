/- @file LeanPlayground/UnivAlg/Basics.lean
 - The basic definitions (especially datatypes) behind this theory of universal algebra.
 -/

/- IMPORTS: -/
-- (none)



/- SECTION: Equational classes (but not their models) -- inital definitions and setup -/

/-- A logical operation (function symbol), specified by an `.id` and `.arity`. -/
structure Operation : Type where
  id    : String
  arity : Nat
deriving Repr
abbrev Op : Type := Operation

/-- A list of operations, each with unique `.id`s. -/
structure Operations : Type where
  list : List Operation
  uqIds : ∀ (i j : Fin list.length), i ≠ j → list.get i ≠ list.get j
deriving Repr
abbrev Ops : Type := Operations

-- TODO:
--  Equations between operation composites in an operation list
--  Equational classes
