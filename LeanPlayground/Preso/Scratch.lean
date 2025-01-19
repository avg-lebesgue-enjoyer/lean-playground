/- @file LeanPlayground/Preso/Scratch.lean
 - Working space for ideas relevant to the preso
 -/
namespace π
universe u

/- SECTION: What is a statement, and what is a proof? -/

-- .; PREREQ: `inductive` types
inductive Statement : Type u where
  | true    : Statement
  | false   : Statement
  | and     : Statement → Statement → Statement
  | or      : Statement → Statement → Statement
  | implies : Statement → Statement → Statement
  | not     : Statement → Statement
  | all     : (α → Statement) → Statement
  | ex      : (α → Statement) → Statement

-- .; PREREQ: `axiom`
-- NOTE: This is kinda messy...
axiom Proof : Statement → Type u
namespace Proof open Statement
  -- `true` is true.
  axiom trueI
    : Proof true
  -- From `false`, you can get anything your heart desires
  axiom falseE {α : Type u}
    : Proof false
    → α
  -- .; PREREQ: (non-dependent) product type `×`
  -- A proof of `φ ∧ ψ` corresponds exactly to a proof of `φ` and a proof of `ψ`
  axiom andI {φ ψ : Statement}
    : Proof φ × Proof ψ
    → Proof (and φ ψ)
  axiom andE {φ ψ : Statement}
    : Proof (and φ ψ)
    → Proof φ × Proof ψ
  -- .; This is better encoded by the PREREQ: sum type `⊕`.
  -- A proof of `φ ∨ ψ` corresponds exactly to a proof of `φ` or a proof of `ψ`
  axiom orIL {φ ψ : Statement}
    : Proof φ
    → Proof (or φ ψ)
  axiom orIR {φ ψ : Statement}
    : Proof ψ
    → Proof (or φ ψ)
  axiom orE {φ ψ : Statement} {α : Type u}
    : Proof (or φ ψ) × (Proof φ → α) × (Proof ψ → α)
    → α
  -- .; This is best encoded by just writing that it's `→`. PREREQ: function types
  -- A proof of `φ → ψ` corresponds exactly to a function between proofs
  axiom impliesI {φ ψ : Statement}
    : (Proof φ → Proof ψ)
    → Proof (implies φ ψ)
  axiom impliesE {φ ψ : Statement}
    : Proof (implies φ ψ)
    → (Proof φ → Proof ψ)
  -- NOTE: This needs some good explanation in the actual talk
  -- A proof of `¬ φ` corresponds exactly to `φ → False`
  axiom notI {φ : Statement}
    : (Proof φ → Proof false)
    → Proof (not φ)
  axiom notE {φ : Statement}
    : Proof (not φ)
    → (Proof φ → Proof false)
  -- .; PREREQ: Dependent function
  -- A `∀` statement is a dependent function
  axiom allI {α : Sort u} {φ : α → Statement}
    : ((a : α) → Proof (φ a))
    → Proof (all φ)
  axiom allE {α : Sort u} {φ : α → Statement}
    : Proof (all φ)
    → ((a : α) → Proof (φ a))
  -- .; PREREQ: Dependent pair
  -- An `∃` statement is a dependent pair
  axiom exI {α : Sort u} {φ : α → Statement}
    : (a : α) → Proof (φ a)
    → Proof (ex φ)
  inductive DepPair (α : Sort u) (β : α → Type u) : Type u where | it : (a : α) → β a → DepPair α β
  axiom exE {α : Sort u} {φ : α → Statement}
    : Proof (ex φ)
    → DepPair α (Proof ∘ φ)
end Proof



/- SECTION: What do I even wanna prove? -/
example {p : Prop}
  : p → p
  := fun h_p => h_p
example {p : Prop}
  : p → ((p → False) → False)
  := fun h_p =>
      fun h_p_2_False =>
        h_p_2_False h_p
example {p : Prop}
  : p → ¬(¬p)
  := fun h_p h_np =>
    h_np h_p
example {p q : Prop}
  : p → q → p ∧ q
  := And.intro
example {p q : Prop}
  : p → p ∨ q
  := Or.inl
#check Or.inr
example {p q : Prop}
  : p ∧ q ∧ p → q
  := fun ⟨_, h_q, _⟩ =>
    h_q
example {p q : Prop}
  : ¬p ∨ ¬q → ¬(p ∧ q)
  := fun h =>
    match h with
    | .inl h_np =>
      h_np ∘ And.left
      -- fun h_pq =>
      --   h_np (And.left h_pq)     -- f (g x) = (f ∘ g)
    | .inr h_nq =>
      h_nq ∘ And.right
      -- fun h_pq =>
      --   h_nq (And.right h_pq)
example {p q : Prop}
  : ¬p ∨ ¬q → ¬(p ∧ q)
  | .inl h_np => h_np ∘ And.left
  | .inr h_nq => h_nq ∘ And.right

example {p q : Prop}
  : ((p → False) → False) → p
  := fun h =>
    sorry

theorem funny {p : Prop}
  : p ∨ ¬p
  := Classical.em p
#print axioms funny

-- .; PREREQ: Introduce `let` and `have` expressions before
example {p : Prop}
  : ¬(¬p) → p
  :=
  fun h_nnp =>
    have h_p_v_np := Classical.em p
    match h_p_v_np with
    | .inl h_p => h_p
    | .inr h_np =>
      have h_f : False := h_nnp h_np
      False.elim h_f

namespace arugmentForms
  variable {p q r : Prop}
  theorem modusPonens
    : (p → q)
    → p
    → q
    := (· ·)
  theorem modusTollens
    : (p → q)
    → ¬q
    → ¬p
    := fun h_p2q h_q2f h_p =>
      h_q2f (h_p2q h_p)
  theorem elimL
    : p ∨ q
    → ¬p
    → q
    := fun h_pvq h_np =>
      match h_pvq with
      | .inl h_p => False.elim <| h_np h_p
      | .inr h_q => h_q
  theorem trans
    : (q → r)
    → (p → q)
    → (p → r)
    := (· ∘ ·)
  theorem byContradiction
    : (¬p → False)
    → p
    := Classical.not_not.mp
end arugmentForms
namespace quantifiers
  variable {α : Type u}
  variable {p : α → Prop}
  theorem not_exists_iff_forall_not
    : ¬ (∃ x : α, p x)
    ↔ (∀ x : α, ¬ (p x))
    := Iff.intro
      ( -- show `((∃ x, p x) → False) → ((x : α) → p x → False)`
        fun h_n_ex x h_px =>
          h_n_ex ⟨x, h_px⟩
      )
      ( -- show `((x : α) → p x → False) → (∃ x, p x) → False`
        fun h_all_n_p h_ex_p =>
          have ⟨x, h_px⟩ := h_ex_p
          h_all_n_p x h_px
      )
  theorem not_forall_iff_exists_not
    : ¬ (∀ x, p x)
    ↔ (∃ x, ¬ p x)
    := Iff.intro
      ( -- show (¬ ∀ x, p x) → (∃ x, ¬ p x)
        -- SPECIAL CASE: x ∈ {a, b};
        --    Write `φ := p a` and `ψ := p b`
        --    `¬ (φ ∧ ψ) → ( ¬ φ ∨ ¬ ψ )`
        Classical.not_forall.mp
      )
      ( -- show (∃ x, ¬ p x) → (¬ ∀ x, p x)
        fun ⟨x, h_n_px⟩ h_all_p =>
          h_n_px (h_all_p x)
      )
end quantifiers



/- SECTION: Logic boring; what else can we do? -/

inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ
deriving Repr -- this means we can `#print` these out
section magic
  def ℕ.asNat : ℕ → Nat | .zero => 0 | .succ n => .succ (ℕ.asNat n)
  def ℕ.raw : ℕ → String | .zero => "ℕ.zero" | .succ n => s!"ℕ.succ ({n.raw})"
  def ℕ.toString (n : ℕ) : String := s!"The term `{n.raw}` encodes the number {n.asNat}"
  def Nat.asℕ : Nat → ℕ | 0 => .zero | .succ n => .succ (Nat.asℕ n)
  instance : ToString ℕ where toString := ℕ.toString
end magic
#eval (ℕ.succ (ℕ.succ ℕ.zero)).toString
#eval (Nat.asℕ 10).toString

def ℕ.add (x y : ℕ) : ℕ :=
  match y with
  | .zero => x
  | .succ y' => .succ (ℕ.add x y')
instance : Add ℕ where add := ℕ.add -- `x + y` is now short for `ℕ.add x y`.

/-- `replicate n a` produces the list `[a, a, ..., a]` with `n` copies of `a`. -/
def replicate : ℕ → α → List α :=
  fun n a =>
    match n with
    | .zero     => []
    | .succ n'  => a :: (replicate n' a)
#eval replicate (Nat.asℕ 10) "ligma"

-- .; I really want to throw in something like:
theorem ℕ.add_assoc {x y z : ℕ}
  : (x + y) + z = x + (y + z)
  := match z with
    | .zero => rfl
    | .succ z' =>
      -- show `(x + y) + .succ z' = x + (y + .succ z')`
      calc (x + y) + .succ z'
        _ = .succ ((x + y) + z')  := Eq.refl ((x + y) + .succ z')
        _ = .succ (x + (y + z'))  := congrArg ℕ.succ (@ℕ.add_assoc x y z')
        _ = x + .succ (y + z')    := Eq.refl (ℕ.succ (x + (y + z')))
        _ = x + (y + .succ z')    := Eq.refl (x + (y + .succ z'))
  #print ℕ.add_assoc
  -- .; BUT we need:
  --    .; PREREQ: `calc` blocks
  --    .; PREREQ: `=` <-- most important!!

#print Eq
inductive Eq' {α : Sort u} : α → α → Prop where
  | refl : (a : α) → Eq' a a
-- Lean's standard library calls this `Eq` and uses the notation `· = ·` instead of `Eq · ·`
#print propext
namespace equality_lessgo
  variable {α : Type}
  variable {a a' b c : α}
  theorem symm
    : a = b
    → b = a
    := fun h_a_eq_b =>
      match h_a_eq_b with
      | .refl _ => rfl -- `rfl := Eq.refl _`
  theorem trans
    : a = b
    → b = c
    → a = c
    := fun h_ab h_bc =>
      match h_bc with
      | .refl _ => h_ab
  theorem congrArg (f : α → β)
    :   a = a'
    → f a = f a'
    := fun h =>
      match h with
      | .refl _ =>
        rfl
end equality_lessgo

example {a b c d : ℕ}
  : a = b
  → b = c
  → d = c
  → ℕ.succ a = ℕ.succ d
  := fun h_ab h_bc h_dc =>
    congrArg ℕ.succ <|
      Eq.trans h_ab <|        -- `a = b`
      Eq.trans h_bc           -- `b = c`
              (Eq.symm h_dc)  -- `c = d`
set_option pp.fieldNotation false -- NOTE: Should probably do this for the preso
theorem gaming {a b c d : ℕ}
  : a = b
  → b = c
  → d = c
  → ℕ.succ a = ℕ.succ d
  := fun h_ab h_bc h_dc =>
    calc ℕ.succ a
      _ = ℕ.succ b   := by rw [h_ab]
      _ = ℕ.succ c   := by rw [h_bc]
      _ = ℕ.succ d   := by rw [← h_dc]
#print gaming -- this proof is disgustingly messy... but no-one cares.
theorem gaming' {a b c d : ℕ} -- NOTE: This is a pretty smooth introduction to tactic mode
  : a = b
  → b = c
  → d = c
  → ℕ.succ a = ℕ.succ d
  := by
    intro h_ab h_bc h_dc
    rw [h_ab, h_bc, ←h_dc]
#print gaming'

-- NOTE: Good examples to work with tactic mode for a bit: *build up to `ℕ.add_comm`*
@[simp]
theorem ℕ.add_zero {x : ℕ}
  : x + .zero = x
  := by
    rfl
@[simp]
theorem ℕ.add_succ {x y : ℕ}
  : x + .succ y = .succ (x + y)
  := by
    rfl
@[simp]
theorem ℕ.zero_add {x : ℕ}
  : .zero + x = x
  := match x with
    | .zero =>
      rfl
    | .succ x' =>
      -- show `zero + succ x' = succ x'`
      calc zero + succ x'
        _ = succ (zero + x')  := ℕ.add_succ
        _ = succ x'           := by rw [@ℕ.zero_add x']
@[simp]
theorem ℕ.succ_add {x y : ℕ}
  : .succ x + y = .succ (x + y)

  := by
    induction y
    case zero => rfl
    case succ y' ih => rw [ℕ.add_succ, ih, ℕ.add_succ]
theorem ℕ.add_comm (x y : ℕ)
  : x + y = y + x
  := by
    induction y
    case zero => simp
    case succ y' ih => simp_all

-- FIXME: Think of more stuff to show off

end π
