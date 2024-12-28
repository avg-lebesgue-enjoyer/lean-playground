/- @file LeanPlayground/Numbers/Integer.lean
 - Proofs regarding the integers.
 -/

/- IMPORTS: ℕ -/
import LeanPlayground.Numbers.Results.Natural
import LeanPlayground.Numbers.Natural

namespace Numbers



/- SECTION: Defining ℤ -/

/-- Equivalence relation governing the transition ℕ ⤳ ℤ. -/
def same_difference : ℕ × ℕ → ℕ × ℕ → Prop
  | (a, b), (x, y) => a + y = x + b

-- Establish that `same_difference` is an `Equivalence` relation
namespace same_difference
  theorem refl (p : ℕ × ℕ) : same_difference p p := rfl
  theorem symm {p q : ℕ × ℕ} : same_difference p q → same_difference q p := by
    intro h ; unfold same_difference at h
    show q.1 + p.2 = p.1 + q.2
    have h : p.1 + q.2 = q.1 + p.2 := h
    exact h.symm
  open ℕ.results in
  theorem trans {p q r : ℕ × ℕ} : same_difference p q → same_difference q r → same_difference p r := by
    intro h_pq h_qr
    have h_pq : p.1 + q.2 = q.1 + p.2 := h_pq
    have h_qr : q.1 + r.2 = r.1 + q.2 := h_qr
    show p.1 + r.2 = r.1 + p.2
    have : p.1 + q.2 + q.1 + r.2 = q.1 + p.2 + r.1 + q.2 := calc p.1 + q.2 + q.1 + r.2
      _ = (p.1 + q.2) + (q.1 + r.2) := by rw [← arithmetic.add_assoc]
      _ = (q.1 + p.2) + (r.1 + q.2) := by rw [h_pq, h_qr]
      _ = q.1 + p.2 + r.1 + q.2     := by rw [arithmetic.add_assoc]
    have : q.1 + (p.1 + q.2 + r.2) = q.1 + (p.2 + r.1 + q.2) :=
      calc q.1 + (p.1 + q.2 + r.2)
        _ = (q.1 + (p.1 + q.2)) + r.2 := by rw [arithmetic.add_assoc]
        _ = ((q.1 + p.1) + q.2) + r.2 := by rw [arithmetic.add_assoc (x := q.1)]
        _ = ((p.1 + q.1) + q.2) + r.2 := by rw [arithmetic.add_comm (x := p.1)]
        _ = (p.1 + (q.1 + q.2)) + r.2 := by rw [← arithmetic.add_assoc (x := p.1)]
        _ = (p.1 + (q.2 + q.1)) + r.2 := by rw [arithmetic.add_comm (x := q.1)]
        _ = p.1 + q.2 + q.1 + r.2     := by rw [arithmetic.add_assoc (x := p.1)]
        _ = q.1 + p.2 + r.1 + q.2     := this
        _ = q.1 + p.2 + (r.1 + q.2)   := by rw [← arithmetic.add_assoc]
        _ = q.1 + (p.2 + (r.1 + q.2)) := by rw [← arithmetic.add_assoc]
        _ = q.1 + (p.2 + r.1 + q.2)   := by rw [arithmetic.add_assoc (x := p.2)]
    have : p.1 + q.2 + r.2 = p.2 + r.1 + q.2 := arithmetic.add_left_cancel this
    have : q.2 + (p.1 + r.2) = q.2 + (p.2 + r.1) :=
      calc q.2 + (p.1 + r.2)
        _ = q.2 + p.1 + r.2   := by rw [arithmetic.add_assoc]
        _ = p.1 + q.2 + r.2   := by rw [@arithmetic.add_comm q.2]
        _ = p.2 + r.1 + q.2   := this
        _ = p.2 + (r.1 + q.2) := by rw [← arithmetic.add_assoc]
        _ = p.2 + (q.2 + r.1) := by rw [@arithmetic.add_comm r.1]
        _ = p.2 + q.2 + r.1   := by rw [arithmetic.add_assoc]
        _ = q.2 + p.2 + r.1   := by rw [@arithmetic.add_comm p.2]
        _ = q.2 + (p.2 + r.1) := by rw [← arithmetic.add_assoc]
    have : p.1 + r.2 = p.2 + r.1 := arithmetic.add_left_cancel this
    conv at this => { rhs; rw [arithmetic.add_comm] }
    assumption
  theorem equivalence : Equivalence same_difference :=
    { refl := refl, symm := symm, trans := trans }
  instance setoid : Setoid (ℕ × ℕ) where
    r := same_difference
    iseqv := equivalence
end same_difference

/-- The integers, defined as `(ℕ × ℕ) ⧸ same_difference`. -/
def ℤ : Type := Quotient same_difference.setoid
/-- Canonical quotient map onto `ℤ := (ℕ × ℕ) ⧸ same_difference`. -/
def ℤ.mk : ℕ × ℕ → ℤ := Quotient.mk same_difference.setoid
/-- The somewhat trivial part of the quotient axiomitisation for `ℤ`. -/
theorem ℤ.exact {p q : ℕ × ℕ} : ℤ.mk p = ℤ.mk q → p ≈ q := by
  intro h
  unfold ℤ.mk at h
  apply Quotient.exact
  assumption
/-- The nontrivial part of the quotient axiomitisation for `ℤ`. -/
theorem ℤ.sound {p q : ℕ × ℕ} : p ≈ q → ℤ.mk p = ℤ.mk q := by
  intro h_same_difference
  unfold ℤ.mk
  apply Quotient.sound
  assumption
/-- The induction principle for `ℤ`: every element may as well be of the form `ℤ.mk (something : ℕ × ℕ)`. -/
theorem ℤ.ind {β : ℤ → Prop} (mk : ∀ (p : ℕ × ℕ), β (ℤ.mk p)) : (z : ℤ) → β z := by
  apply Quotient.ind
  intro a
  apply mk
/-- "Pattern-matching" the provided argument as `ℤ.mk (something : ℕ × ℕ)` *in a proof*. See also `ℤ.ind`. -/
theorem ℤ.indOn {β : ℤ → Prop} (z : ℤ) (mk : ∀ (p : ℕ × ℕ), β (ℤ.mk p)) : β z := ℤ.ind mk z
/--
  Lift a non-dependent single-argument function `ℕ × ℕ → β` which respects the quotienting relation
  `same_difference` to a map `ℤ → β`.
-/
def ℤ.lift {β : Sort u} (f : ℕ × ℕ → β) : (∀ (p q : ℕ × ℕ), p ≈ q → f p = f q) → ℤ → β :=
  Quotient.lift (α := ℕ × ℕ) (β := β) (s := same_difference.setoid) f

instance : OfNat ℤ 0 where ofNat := ℤ.mk (0, 0)
instance : OfNat ℤ 1 where ofNat := ℤ.mk (1, 0)

namespace ℤ
  /- SECTION: Coersion `ℕ ↪ ℤ` -/
  namespace coe_from_ℕ
    instance it : Coe ℕ ℤ where coe x := ℤ.mk (x, 0)
  end coe_from_ℕ



  /- SECTION: Notation `0` and `1` -/
  theorem ntn_zero : ℤ.mk (0, 0) = 0 := rfl
  theorem ntn_one : ℤ.mk (1, 0) = 1 := rfl



  /- SECTION: Addition: Definition, assoc, comm, kill `0` -/
  def pair_add : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ :=
    fun ⟨a, b⟩ ⟨x, y⟩ => ⟨a + x, b + y⟩

  open ℕ.results in
  theorem pair_add.hom
    {p p' q q' : ℕ × ℕ}
    : p ≈ p'
    → q ≈ q'
    → pair_add p q ≈ pair_add p' q'
    := by
      let ⟨a, b⟩ := p ; let ⟨a', b'⟩ := p' ; let ⟨x, y⟩ := q ; let ⟨x', y'⟩ := q'
      intro (h_p : a + b' = a' + b) (h_q : x + y' = x' + y)
      show (a + x) + (b' + y') = (a' + x') + (b + y)
      calc (a + x) + (b' + y')
        _ = ((a + x) + b') + y' := by rw [arithmetic.add_assoc]
        _ = (a + (x + b')) + y' := by rw [← @arithmetic.add_assoc a]
        _ = (a + (b' + x)) + y' := by rw [arithmetic.add_comm x]
        _ = ((a + b') + x) + y' := by rw [@arithmetic.add_assoc a]
        _ = (a + b') + (x + y') := by rw [← arithmetic.add_assoc]
        _ = (a' + b) + (x' + y) := by rw [h_p, h_q]
        _ = ((a' + b) + x') + y := by rw [arithmetic.add_assoc]
        _ = (a' + (b + x')) + y := by rw [← @arithmetic.add_assoc a']
        _ = (a' + (x' + b)) + y := by rw [arithmetic.add_comm b]
        _ = ((a' + x') + b) + y := by rw [@arithmetic.add_assoc a']
        _ = (a' + x') + (b + y) := by rw [← arithmetic.add_assoc]

  /-- Addition on `ℤ`. Defined by lifting to the quotient. -/
  def add (x : ℤ) (y : ℤ) : ℤ :=
    Quotient.liftOn₂ x y
      (fun p q => ℤ.mk $ pair_add p q)
      $ by -- Proof that `ℤ.mk ∘ pair_add` (put in necessary currying/uncurrying to make that typecheck) respects `same_difference`
        intro p q p' q' h_p h_q
        show ℤ.mk (pair_add p q) = ℤ.mk (pair_add p' q')
        apply ℤ.sound
        apply pair_add.hom <;> assumption
  instance instAdd : Add ℤ where add := ℤ.add
  namespace arith -- now we can finally prove stuff about addition on `ℤ` lol
    /-- The defining property of `ℤ.add`: it acts as pairwise addition on arguments of the form `ℤ.mk (thing : ℕ × ℕ)`. -/
    theorem add_mk {a b x y : ℕ} : (ℤ.mk (a, b)) + (ℤ.mk (x, y)) = ℤ.mk (a + x, b + y) := by
      show ℤ.add (ℤ.mk (a, b)) (ℤ.mk (x, y)) = ℤ.mk (a + x, b + y)
      unfold ℤ.mk
      unfold ℤ.add
      rfl -- thank heavens this worked... This is because `Quotient.liftOn₂` knows what it does to `Quotient.mk`s as arguments.

    -- NOTE: Associativity
    theorem add_assoc {x y z : ℤ} : x + (y + z) = (x + y) + z := by
      -- Grab representatives
      apply ℤ.indOn x ; intro (a, b)
      apply ℤ.indOn y ; intro (p, q)
      apply ℤ.indOn z ; intro (x, y)
      -- Do the thing with the representatives (the thing, in this case, is to just use `ℕ.add`'s associativity)
      rw [add_mk, add_mk, add_mk, add_mk]
      conv => { lhs ; arg 1 ; congr <;> rw [ℕ.results.arithmetic.add_assoc] }

    -- NOTE: Commutativity
    theorem add_comm (x y : ℤ) : x + y = y + x := by
      -- Grab representatives
      apply ℤ.indOn x ; intro ⟨a, b⟩
      apply ℤ.indOn y ; intro ⟨x, y⟩
      -- Do the thing with the representatives
      rw [add_mk, add_mk]
      conv => { lhs ; arg 1 ; congr <;> rw [ℕ.results.arithmetic.add_comm] }

    -- NOTE: The two kill-`0` axioms
    theorem add_zero {x : ℤ} : x + 0 = x := by
      apply ℤ.indOn x ; intro ⟨a, b⟩
      rw [← ntn_zero]
      rw [add_mk]
      conv => { lhs ; arg 1 ; congr <;> rw [ℕ.results.arithmetic.add_zero] }
    theorem zero_add {x : ℤ} : 0 + x = x := by
      rw [add_comm]
      exact add_zero
  end arith



  /- SECTION: Negation: Definition, double negation, inverse to `ℤ.add` -/
  /-- Negation on `ℤ`. -/
  def neg : ℤ → ℤ :=
    ℤ.lift (fun (a, b) => ℤ.mk (b, a)) $ by -- Proof that this respects the relation
      intro (a, b) (x, y) (h_pq : a + y = x + b)
      show ℤ.mk (b, a) = ℤ.mk (y, x)
      apply ℤ.sound
      show b + x = y + a
      conv => { congr <;> rw [ℕ.results.arithmetic.add_comm]}
      exact h_pq.symm
  instance : Neg ℤ where neg := ℤ.neg
  namespace arith
    /-- The defining property of `ℤ.neg`: it swaps the components of a `thing : ℕ × ℕ` when applied to `ℤ.mk thing`. -/
    theorem neg_mk {a b : ℕ} : - ℤ.mk (a, b) = ℤ.mk (b, a) := rfl

    /-- Double negation for `ℤ`. -/
    theorem neg_neg {x : ℤ} : - (-x) = x := by
      apply ℤ.indOn x ; intro (a, b)
      rw [neg_mk, neg_mk]

    /-- `ℤ.neg` forms right-inverses for `ℤ.add`. -/
    theorem add_neg {x : ℤ} : x + (-x) = 0 := by
      apply ℤ.indOn x ; intro (a, b)
      rw [neg_mk, add_mk, ←ntn_zero]
      apply ℤ.sound
      show (a + b) + 0 = 0 + (b + a)
      open ℕ.results in
      rw [arithmetic.add_zero, arithmetic.zero_add, arithmetic.add_comm]

    /-- `ℤ.neg` forms left-inverses for `ℤ.add`. -/
    theorem neg_add {x : ℤ} : (-x) + x = 0 := by
      rw [add_comm]
      exact add_neg
  end arith



  /- SECTION: Multiplication: Definition, assoc, comm -/
  def pair_mul : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
    | (a, b), (x, y) =>
      (a * x + b * y, a * y + b * x)

  /-- Multiplication on `ℤ`. Defined by lifting to the quotient. -/
  open ℕ.results in
  def mul (x : ℤ) (y : ℤ) : ℤ :=
    Quotient.liftOn₂ x y
      (fun p q => ℤ.mk $ pair_mul p q)
      $ by -- Proof that `ℤ.mk ∘ pair_mul` (put in necessary currying/uncurrying to make that typecheck) respects `same_difference`
        intro ⟨a, b⟩ ⟨x, y⟩ ⟨a', b'⟩ ⟨x', y'⟩ (h_ab : a + b' = a' + b) (h_xy : x + y' = x' + y)
        show ℤ.mk (pair_mul (a, b) (x, y)) = ℤ.mk (pair_mul (a', b') (x', y'))
        apply ℤ.sound
        show (a * x + b * y, a * y + b * x) ≈ (a' * x' + b' * y', a' * y' + b' * x')
        show (a * x + b * y) + (a' * y' + b' * x') = (a' * x' + b' * y') + (a * y + b * x)
        rw [← ℕ.results.arithmetic.add_assoc]
        apply @ℕ.results.arithmetic.add_right_cancel (b' * x)
        rw  [ ← ℕ.results.arithmetic.add_assoc
            ,   ℕ.results.arithmetic.add_comm _ (b' * x)
            ,   ℕ.results.arithmetic.add_assoc
            , ← ℕ.results.arithmetic.add_mul
            ,   h_ab]
        apply @ℕ.results.arithmetic.add_right_cancel (a * x')
        rw  [ ← ℕ.results.arithmetic.add_assoc
            , ← @ℕ.results.arithmetic.add_assoc (b * y)
            , ← @ℕ.results.arithmetic.add_assoc (a' * y')
            , ← ℕ.results.arithmetic.add_mul
            ,   ℕ.results.arithmetic.add_comm b'
            ,   h_ab]
        repeat (first | rw [ℕ.results.arithmetic.add_assoc] | rw [ℕ.results.arithmetic.add_mul])
        conv => {
          lhs;lhs;lhs
          rw  [ ← arithmetic.add_assoc
              , ← arithmetic.add_assoc
              ,   arithmetic.add_comm (b * y)
              ,   @arithmetic.add_assoc (b * x)
              ,   arithmetic.add_comm (b * x)
              ,   arithmetic.add_assoc
              ,   arithmetic.add_assoc
              , ← arithmetic.mul_add
              ,   h_xy
              ,   arithmetic.mul_add]
        }
        suffices a' * y + b * x + b * y + a' * x' + b * x' = b' * y' + a * y + b * x + b' * x + a * x' by
          repeat rw [← arithmetic.add_assoc]
          conv => {
            congr <;> ( arg 2 ; repeat rw [arithmetic.add_assoc] )
          }
          rw [this]
        apply @arithmetic.add_right_cancel (b * y')
        repeat rw [← arithmetic.add_assoc]

        admit
  instance instMul : Mul ℤ where mul := ℤ.mul

end ℤ

end Numbers
