/-
  **FILE** `LeanPlayground/Preso/4Interactively.lean`
  **PURPOSE** Introduction to interactive proof
-/

/- IMPORTS: -/

import LeanPlayground.Preso.«3Proving»
set_option pp.fieldNotation false
namespace σ



/- TEST: Scratch crap that shouldn't be left here -/
-- NOTE: Files `3Proving.lean`, `4Interactively.lean` and `5Automatically.lean` should all be aggregated into one file.
-- Using the infoview is already interactive theorem proving, and putting a hard cut right after `congrArg` would
--  damage the flow of the presentation.

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ

def ℕ.add : ℕ → ℕ → ℕ :=
  fun x y => -- Compute `x + y`
    match y with
    | zero    => x                  -- `x + 0 = x`
    | succ y' => succ (ℕ.add x y')  -- `x + (one more than y) = one more than (x + y)`
instance : Add ℕ where add := ℕ.add -- `x + y` now means `ℕ.add x y`

theorem ℕ.add_zero : ∀ (x : ℕ), x + zero = x := by intro x ; rfl
theorem ℕ.add_succ : ∀ (x y : ℕ), x + succ y = succ (x + y) := by intro x y ; rfl

-- Example of `rw` (and thus `congrArg`)
theorem ℕ.add_assoc
  : ∀ (x y z : ℕ), x + (y + z) = (x + y) + z
  := by
    intro x y z -- `fun x y z =>`
    -- Proof by induction:
    -- True when `z = zero`
    -- If true for `z'`, then true when `z = succ z'`.
    match z with
    | zero =>
      -- `congrArg (fun a => x + a) (ℕ.add_zero y)`
      rw [ℕ.add_zero, ℕ.add_zero]
    | succ z' =>
      -- INDUCTIVE HYPOTHESIS: `ℕ.add_assoc x y z' : x + (y + z') = (x + y) + z'`
      rw [ℕ.add_succ, ℕ.add_succ, ℕ.add_assoc, ℕ.add_succ]

-- Example of `simp`
theorem ℕ.add_assoc'
  : ∀ (x y z : ℕ), x + (y + z) = (x + y) + z
  := by
    intro x y z -- `fun x y z =>`
    -- Proof by induction:
    -- True when `z = zero`
    -- If true for `z'`, then true when `z = succ z'`.
    match z with
    | zero =>
      -- `congrArg (fun a => x + a) (ℕ.add_zero y)`
      -- rw [ℕ.add_zero, ℕ.add_zero]
      simp [ℕ.add_zero]
      -- sorry
    | succ z' =>
      -- INDUCTIVE HYPOTHESIS: `ℕ.add_assoc x y z' : x + (y + z') = (x + y) + z'`
      -- rw [ℕ.add_succ, ℕ.add_succ, ℕ.add_assoc, ℕ.add_succ]
      simp [ℕ.add_succ, ℕ.add_assoc]

-- NOTE: Only include if I get time
-- ⚠: Yeah definitely cut this out (hide it way and `import` it)
-- We define functions on `inductive` data types using **recursion**:
def List.get'? : List α → Nat → Option α :=
  fun as n =>
  match as with
  | [] => none
  | (a :: as') =>
    match n with
    | .zero => a
    | .succ n' => List.get'? as' n' -- The `1 + n'`th element of `a :: as'` is the `n'`th element of `as'`.

-- Demoing this with just automation might actually be pretty cool...
-- ⚠: No, that would take too long.
theorem List.get'?_in_bounds
  : ∀ (as : List α) (i : Nat),
      i < List.length as
      → List.get'? as i ≠ none
  := by
    intro as
    induction as <;> simp_all
    intro i h
    simp [get'?]
    split <;> simp_all
    -- [done.]
#print List.get'?_in_bounds
-- But *this* is good (and it's the punchline, too)
-- [6.] Yeah, I'm definitely keeping this in.
def List.get' : (as : List α) → (i : Nat) → (h : i < List.length as) → α :=
  fun as i h =>
    match h_rep: List.get'? as i with
    | some a => a
    | none => False.elim (by simp_all [List.get'?_in_bounds])
-- NOTE: The equivalents in Haskell and Java crash the program with an error
-- NOTE: The equivalent in C is quite possibly a *security vulnerability*
end σ

-- FIXME: Turn `2Programming.lean`, `3Proving.lean` and `4Interactively.lean` into two files -- one skeleton and
--         one solution -- and try to keep it concise.

-- [7.] Time permitting, add the following stuff into this file (or just keep it in just in case, in a `section` that gets folded up)
--    An example of my own work (`(ℤ⧸p)` or *Thm. Fund Arith*)
--    Some Isabelle?
