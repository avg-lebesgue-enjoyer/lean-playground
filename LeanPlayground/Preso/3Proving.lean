/-
  **FILE** `LeanPlayground/Preso/3Proving.lean`
  **PURPOSE** Introduction to proving
-/

/- IMPORTS: -/
import LeanPlayground.Preso.«2Programming»
set_option pp.fieldNotation false
set_option linter.unusedVariables false
namespace ν



/- TEST: Scratch crap that shouldn't be left here -/

-- TODO: Introduce aspects of proof that I've marked on the whiteboard

-- NOTE: `PROOF : STATEMENT`.

-- NOTE: `∧` (AND) is essentially the **product**.
inductive And (p q : Prop) : Prop where
  | intro : p → q → And p q
-- `p ∧ q` may as well be `p × q`.
theorem And.intro_other_order (p q : Prop)
  : q → p → p ∧ q
  := fun h_q h_p =>
    _root_.And.intro h_p h_q

-- NOTE: `∨` (OR) is essentially the **sum**.
inductive Or (p q : Prop) : Prop where
  | inl : p → Or p q
  | inr : q → Or p q
-- `p ∨ q` may as well be `p ⊕ q`
theorem Or.symm (p q r : Prop)
  : p ∨ q → q ∨ p
  := fun h_pvq =>
    match h_pvq with
    | _root_.Or.inl h_p => _root_.Or.inr h_p
    | _root_.Or.inr h_q => _root_.Or.inl h_q

-- NOTE: `→` (IMPLIES) is a **function type**.
inductive Implies (p q : Prop) : Prop where
  | intro : (p → q) → Implies p q

#check Or.symm

-- NOTE: Should go first
inductive True : Prop where
  | intro : True

-- NOTE: Should also go first
inductive False : Prop -- no constructors

-- NOTE: `¬` (NOT) has a funny definition
-- (Consider cutting? No...)
def Not (p : Prop) : Prop := p → False

-- NOTE: `∀ (a : α), p a`
-- (*Definitely* keep in.)
def Forall (α : Type) (p : α → Prop) : Prop :=
  (a : α) → p a
-- Fix arbitrary `a : α`
-- ..... (some proof here) .....
-- Therefore, `p a` is true
end ν
-- That's it for logic; I just don't have enough time to do more.
namespace τ

-- Yeah equality goes next; just send it mate
#print Eq
inductive Eq {α : Type} : α → α → Prop where
  | refl : (a : α) → Eq a a

-- `a = b` <~~ **MUST USE `refl`**
-- so only proofs: `a = a`
-- Encodes *definitional equality* (terms being "literally the same because *that's how they were defined*")
--  into a *propositional equality* that Lean can manipulate (the `Eq` type)
#check (1 = 3)
end τ
namespace μ

-- Example theorem with equality:
theorem one_eq_one : 1 = 1 := Eq.refl 1
theorem one_add_two_eq_three : 1 + 2 = 3 := show 3 = 3 from Eq.refl 3
theorem add_left_congr -- NOTE: Don't demonstrate this. `congrArg` is the same thing, and this wastes time that could be spent on proof automation instead.
  : ∀ (x y z : Nat),
  -- : (x y z : Nat) →
      x = y → x + z = y + z
  :=
  fun x y z =>
    fun h_x_eq_y =>
      match h_x_eq_y with
      | Eq.refl x =>
        Eq.refl (x + z)

-- Example of why `Eq` is so magical:
theorem congrArg
  (a₁ a₂ : α)
  (f : α → β)
  :   a₁ = a₂
  → f a₁ = f a₂
  := fun h_a₁_eq_a₂ =>
    match h_a₁_eq_a₂ with
    | Eq.refl _ => Eq.refl (f a₁)
-- NOTE: ^^gives a good segue into the `rw` tactic
