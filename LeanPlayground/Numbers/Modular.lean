/- @file LeanPlayground/Numbers/Modular.lean
 - The theory of `ℤ ⧸ m` for `m : ℤ`.
 -/

/- IMPORTS: ℕ -/
import LeanPlayground.Numbers.Results.Natural
import LeanPlayground.Numbers.Natural
import LeanPlayground.Numbers.Results.Integer
import LeanPlayground.Numbers.Integer

namespace Numbers



/- SECTION: Defining ℤ ⧸ m -/

/-- Equivalence relation governing the transition ℤ → ℤ ⧸ m. -/
def same_remainder (m : ℤ) : ℤ → ℤ → Prop
  | x, y => m ∣ y - x

-- Establish that `same_remainder` is an `Equivalence` relation
namespace same_remainder
  open Numbers.ℤ.results

  theorem refl {m : ℤ} (z : ℤ) : same_remainder m z z := by
    show m ∣ z - z
    rw [Numbers.ℤ.results.ring.sub_self]
    exact Numbers.ℤ.results.number_theory.divides_zero m
  theorem symm {m x y : ℤ} : same_remainder m x y → same_remainder m y x := by
    intro (h : m ∣ y - x)
    show m ∣ x - y
    rw  [ ← number_theory.divides_iff_divides_neg
        , ring.sub_eq_add_neg
        , ring.neg_add'
        , ring.neg_neg
        , ring.add_comm
        , ←ring.sub_eq_add_neg]
    assumption
  theorem trans {m x y z : ℤ} : same_remainder m x y → same_remainder m y z → same_remainder m x z := by
    intro (h_xy : m ∣ y - x) (h_yz : m ∣ z - y)
    show m ∣ z - x
    conv => {
      rhs
      calc z - x
        _ = z + -x            := by rw [ring.sub_eq_add_neg]
        _ = z + -x + (-y + y) := by conv => { rhs; rw [ring.neg_add, ring.add_zero] }
        _ = z + -x + -y + y   := by rw [ring.add_assoc]
        _ = z + -y + y + -x   := by repeat rw [← ring.add_right_comm (-x)]
        _ = z - y + (y + -x)  := by conv => { rhs; rw [ring.sub_eq_add_neg, ring.add_assoc]}
        _ = z - y + (y - x)   := by rw [← ring.sub_eq_add_neg]
    }
    apply number_theory.divides_sum <;> assumption

  theorem equivalence {m : ℤ} : Equivalence (same_remainder m) :=
    { refl := refl, symm := symm, trans := trans }
  instance setoid (m : ℤ) : Setoid ℤ where
    r := same_remainder m
    iseqv := equivalence
end same_remainder

/-- The integers modulo an integer. `ℤ ⧸ m` is defined as `ℤ ⧸ same_remainder m`. -/
def ℤMod (m : ℤ) : Type := Quotient (same_remainder.setoid m)
@[inherit_doc] notation:max "ℤ ⧸ " m => ℤMod m
/-- Canonical quotient map onto `ℤ ⧸ m := ℤ ⧸ same_remainder m`. -/
def ℤMod.mk {m : ℤ} : ℤ → ℤ ⧸ m := Quotient.mk (same_remainder.setoid m)

/-- The somewhat trivial part of the quotient axiomitisation for `ℤ ⧸ m`. -/
theorem ℤMod.exact {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk y → same_remainder m x y := by
  intro h
  unfold ℤMod.mk at h
  apply Quotient.exact (s := same_remainder.setoid m)
  assumption

/-- The nontrivial part of the quotient axiomitisation for `ℤ ⧸ m`. -/
theorem ℤMod.sound {m x y : ℤ} : same_remainder m x y → (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk y := by
  intro h
  apply Quotient.sound (s := same_remainder.setoid m)
  assumption

/-- The quotient axiomitisation for `ℤ ⧸ m`, stated in an `↔` form so that it may be used by `rw`. -/
theorem ℤMod.quotax {m x y : ℤ} : same_remainder m x y ↔ (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk y := by
  constructor
  case mp  => exact ℤMod.sound
  case mpr => exact ℤMod.exact

/--
  The induction principle for `ℤ ⧸ m`: every element may as well be of the form `ℤMod.mk (something : ℤ)`.

  For more extensive documentation, see `ℤMod.indOn`
-/
theorem ℤMod.ind {m : ℤ} {β : (ℤ ⧸ m) → Prop} (mk : ∀ (z : ℤ), β (ℤMod.mk z)) : (a : ℤ ⧸ m) → β a := by
  apply Quotient.ind
  intro a
  exact mk a

/--
  "Pattern-matching" the provided argument as `ℤMod.mk (something : ℤ)`. See also `ℤ.ind`.

  A common mnemonic to use in tactic mode is `apply ℤMod.indOn a ; intro z` which "grabs a
    representative `z` for `a`", in the sense that it replaces `a` with `ℤMod.mk z`.
  Alternatively, one can think of this as "pattern-matching" `a` with the "constructor"-based
    pattern `ℤMod.mk z`. Thought of in this way, this mnemonic should be used any time you want
    to write `let ℤMod.mk z := a` or `match a with | ℤMod.mk z =>` etc.
  Consider also using the existence versions `ℤMod.existsRep` and `ℤMod.existsCanonRep`.
-/
theorem ℤMod.indOn {m : ℤ} (a : ℤ ⧸ m) {β : (ℤ ⧸ m) → Prop} (mk : ∀ (z : ℤ), β (ℤMod.mk z)) : β a := ℤMod.ind mk a

/-- Existence form of `ℤ.indOn`. -/
theorem ℤMod.existsRep {m : ℤ} (a : ℤ ⧸ m) : ∃ (z : ℤ), a = ℤMod.mk z := by
  apply a.indOn ; intro z
  exists z

/-- "Less than the modulus" representatives in `ℤ ⧸ n` for `n : ℕ` such that `n ≠ 0`. -/
theorem ℤMod.existsCanonRep {n : ℕ} (h_n_ne_zero : n ≠ 0) (a : ℤ ⧸ n) : ∃ (r : ℕ), a = ℤMod.mk r ∧ r < n := by
  apply a.indOn ; intro z
  have h_0_lt_n : 0 < (n : ℤ) := by
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero]
    exists n
  have ⟨q, r, h_qr, h_r⟩ := Numbers.ℤ.results.number_theory.euclidean_division n z h_0_lt_n |> And.left
  exists r
  constructor
  · apply ℤMod.sound
    show n ∣ r - z
    exists -q
    rw  [ h_qr
        , ℤ.results.ring.sub_eq_add_neg
        , ℤ.results.ring.neg_add'
        , ℤ.results.ring.add_assoc
        , ℤ.results.ring.add_right_comm
        , ℤ.results.ring.add_neg
        , ℤ.results.ring.zero_add
        , ℤ.results.ring.neg_mul_right]
  · rw [ℤ.results.coe_ℕ.coe_ℕ_hom_lt]
    assumption

/--
  Lift a non-dependent single-argument function `ℤ → β` which respects the quotienting relation
  `same_remainder m` to a map `(ℤ ⧸ m) → β`.
-/
def ℤMod.lift {m : ℤ} {β : Sort u} (f : ℤ → β) : (∀ (x y : ℤ), same_remainder m x y → f x = f y) → (ℤ ⧸ m) → β :=
  Quotient.lift f (s := same_remainder.setoid m)

instance {m : ℤ} : OfNat (@ℤMod m) 0 where ofNat := ℤMod.mk 0
instance {m : ℤ} : OfNat (@ℤMod m) 1 where ofNat := ℤMod.mk 1



namespace ℤMod
  /- SECTION: Notation `0` and `1` -/
  theorem ntn_zero {m : ℤ} : (ℤMod.mk 0 : ℤ ⧸ m) = 0 := rfl
  theorem ntn_one {m : ℤ} : (ℤMod.mk 1 : ℤ ⧸ m) = 1 := rfl



  /- SECTION: Coersion `ℕ → ℤ → ℤ ⧸ m` -/
  section coe
    instance fromℤ {m : ℤ} : Coe ℤ (ℤ ⧸ m) where coe := ℤMod.mk
    instance fromℕ {m : ℤ} : Coe ℕ (ℤ ⧸ m) where coe := fromℤ.coe ∘ ℤ.coe_from_ℕ.it.coe
  end coe



  /- SECTION: Addition: definition, assoc, comm, + 0, 0 + -/
  def add {m : ℤ} : (ℤ ⧸ m) → (ℤ ⧸ m) → (ℤ ⧸ m) :=
    let add₁₂ (x y : ℤ) : ℤ ⧸ m := ℤMod.mk (x + y)
    have add₁₂_respects (x : ℤ) : ∀ (y z : ℤ), same_remainder m y z → add₁₂ x y = add₁₂ x z := by
      intro y z (h : m ∣ z - y)
      unfold add₁₂
      apply ℤMod.sound
      show m ∣ (x + z) - (x + y)
      open ℤ.results.ring in
      rw [sub_eq_add_neg, neg_add', add_assoc, add_right_comm (-x), add_neg, zero_add, sub_eq_add_neg.symm]
      assumption
    let add₁ (x : ℤ) : (ℤ ⧸ m) → (ℤ ⧸ m) := ℤMod.lift (add₁₂ x) (add₁₂_respects x)
    have add₁_respects : ∀ (x y : ℤ), same_remainder m x y → add₁ x = add₁ y := by
      intro x y (h : m ∣ y - x)
      have h_ligma : add₁₂ x = add₁₂ y := by
        apply funext ; intro z
        unfold add₁₂
        apply ℤMod.sound
        show m ∣ (y + z) - (x + z)
        open ℤ.results.ring in
        rw [sub_eq_add_neg, neg_add', add_assoc, add_right_comm, ←add_assoc (z := -z), add_neg, add_zero, ←sub_eq_add_neg]
        assumption
      apply funext ; intro z' ; apply z'.indOn ; intro z
      unfold add₁
      show add₁₂ x z = add₁₂ y z
      rw [‹add₁₂ x = add₁₂ y›]
    ℤMod.lift add₁ add₁_respects
  instance instAdd {m : ℤ} : Add (ℤ ⧸ m) where add := ℤMod.add
  namespace arith
    /-- Defining rule -/
    theorem add_mk {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) + (ℤMod.mk y) = ℤMod.mk (x + y) := rfl

    @[simp]
    theorem add_assoc {m : ℤ} {x y z : ℤ ⧸ m} : x + (y + z) = (x + y) + z := by
      apply x.indOn ; intro x'
      apply y.indOn ; intro y'
      apply z.indOn ; intro z'
      simp [add_mk, ℤ.results.ring.spec.add_assoc]

    theorem add_comm {m : ℤ} (x y : ℤ ⧸ m) : x + y = y + x := by
      apply x.indOn ; intro x'
      apply y.indOn ; intro y'
      simp [add_mk, ℤ.results.ring.spec.add_comm]

    theorem add_right_comm {m : ℤ} {x y : ℤ ⧸ m} (z : ℤ ⧸ m) : x + y + z = x + z + y := by
      rw [← add_assoc, add_comm y, add_assoc]

    @[simp]
    theorem add_zero {m : ℤ} {x : ℤ ⧸ m} : x + 0 = x := by
      apply x.indOn ; intro x'
      simp [←ntn_zero, add_mk, ℤ.results.ring.spec.add_zero]
    @[simp]
    theorem zero_add {m : ℤ} {x : ℤ ⧸ m} : 0 + x = x := by
      rw [add_comm]
      exact add_zero
  end arith



  /- SECTION: Negation: definition, other cool stuff -/
  def neg {m : ℤ} : (ℤ ⧸ m) → (ℤ ⧸ m) :=
    let neg₁ (x : ℤ) : ℤ ⧸ m := ℤMod.mk (-x)
    have neg₁_respects : ∀ (x y : ℤ), same_remainder m x y → neg₁ x = neg₁ y := by
      intro x y (_ : m ∣ y - x)
      unfold neg₁ ; apply ℤMod.sound
      show m ∣ (-y) - (-x)
      open ℤ.results.ring in
      rw [sub_neg, ←ℤ.results.number_theory.divides_iff_divides_neg, neg_add', neg_neg, ←sub_eq_add_neg]
      assumption
    ℤMod.lift neg₁ neg₁_respects
  instance instNeg {m : ℤ} : Neg (ℤ ⧸ m) where neg := ℤMod.neg
  namespace arith
    /-- Defining property -/
    theorem neg_mk {m x : ℤ} : - (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk (-x) := rfl

    @[simp]
    theorem neg_neg {m : ℤ} {x : ℤ ⧸ m} : - - x = x := by
      apply x.indOn ; intro x'
      simp [neg_mk, ℤ.results.ring.neg_neg]

    @[simp]
    theorem add_neg {m : ℤ} {x : ℤ ⧸ m} : x + -x = 0 := by
      apply x.indOn ; intro x'
      simp [neg_mk, add_mk, ℤ.results.ring.spec.add_neg, ntn_zero]
    @[simp]
    theorem neg_add {m : ℤ} {x : ℤ ⧸ m} : -x + x = 0 := by
      rw [add_comm]
      exact add_neg

    @[simp]
    theorem neg_add' {m : ℤ} {x y : ℤ ⧸ m} : - (x + y) = -x + -y := by
      apply x.indOn ; intro x'
      apply y.indOn ; intro y'
      simp [add_mk, neg_mk, ℤ.results.ring.neg_add']
    @[simp]
    theorem neg_zero {m : ℤ} : - (0 : ℤ ⧸ m) = 0 := by
      simp [←ntn_zero, neg_mk, ℤ.results.ring.neg_zero]
  end arith



  /- SECTION: Multiplication: definition, assoc, comm, * 1, 1 *, * 0, 0 *  -/
  def mul {m : ℤ} : (ℤ ⧸ m) → (ℤ ⧸ m) → (ℤ ⧸ m) :=
    let mul₁₂ (a b : ℤ) : ℤ ⧸ m := a * b -- coe
    have mul₁₂_respects (a b c : ℤ) : same_remainder m b c → mul₁₂ a b = mul₁₂ a c := by
      intro (h : m ∣ c - b)
      apply ℤMod.sound
      show m ∣ a * c - a * b
      rw [← ℤ.results.ring.mul_sub]
      apply ℤ.results.number_theory.divides_mul_right
      assumption
    let mul₁ (a : ℤ) : (ℤ ⧸ m) → (ℤ ⧸ m) := ℤMod.lift (mul₁₂ a) (mul₁₂_respects a)
    have mul₁_respects (a b : ℤ) : same_remainder m a b → mul₁ a = mul₁ b := by
      intro (h : m ∣ b - a)
      apply funext ; intro z ; apply z.indOn ; intro c
      show mul₁₂ a c = mul₁₂ b c
      apply ℤMod.sound
      show m ∣ b * c - a * c
      rw [← ℤ.results.ring.sub_mul]
      apply ℤ.results.number_theory.divides_mul
      assumption
    ℤMod.lift mul₁ mul₁_respects
  instance instMul {m : ℤ} : Mul (ℤ ⧸ m) where mul := ℤMod.mul
  namespace arith
    /-- Defining property -/
    theorem mul_mk {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) * (ℤMod.mk y) = ℤMod.mk (x * y) := rfl

    @[simp]
    theorem mul_assoc {m : ℤ} {x y z : ℤ ⧸ m} : x * (y * z) = (x * y) * z := by
      apply x.indOn ; intro a
      apply y.indOn ; intro b
      apply z.indOn ; intro c
      simp [mul_mk, ℤ.results.ring.spec.mul_assoc]

    theorem mul_comm {m : ℤ} (x y : ℤ ⧸ m) : x * y = y * x := by
      apply x.indOn ; intro a
      apply y.indOn ; intro b
      simp [mul_mk, ℤ.results.ring.spec.mul_comm]

    theorem mul_right_comm {m : ℤ} {x y : ℤ ⧸ m} (z : ℤ ⧸ m) : x * y * z = x * z * y := by
      rw [← mul_assoc, mul_comm y, mul_assoc]

    @[simp]
    theorem mul_one {m : ℤ} {x : ℤ ⧸ m} : x * 1 = x := by
      apply x.indOn ; intro a
      simp [← ntn_one, mul_mk, ℤ.results.ring.spec.mul_one]
    @[simp]
    theorem one_mul {m : ℤ} {x : ℤ ⧸ m} : 1 * x = x := by
      simp [mul_comm]

    @[simp]
    theorem mul_zero {m : ℤ} {x : ℤ ⧸ m} : x * 0 = 0 := by
      apply x.indOn ; intro a
      simp [← ntn_zero, mul_mk, ℤ.results.ring.mul_zero]
    @[simp]
    theorem zero_mul {m : ℤ} {x : ℤ ⧸ m} : 0 * x = 0 := by
      simp [mul_comm]
  end arith



  /- SECTION: Distributivity -/
  namespace arith
    @[simp]
    theorem mul_add {m : ℤ} {x y z : ℤ ⧸ m} : x * (y + z) = x * y + x * z := by
      apply x.indOn ; intro a
      apply y.indOn ; intro b
      apply z.indOn ; intro c
      simp [add_mk, mul_mk, ℤ.results.ring.spec.mul_add]
    @[simp]
    theorem add_mul {m : ℤ} {x y z : ℤ ⧸ m} : (x + y) * z = x * z + y * z := by
      simp [mul_comm]
  end arith




  /- SECTION: Arithmetic homs re. coersion `ℕ → ℤ → ℤ ⧸ m` -/
end ℤMod

end Numbers
