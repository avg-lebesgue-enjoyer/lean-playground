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

    @[simp]
    theorem neg_inj {m : ℤ} {x y : ℤ ⧸ m} : -x = -y ↔ x = y := by
      constructor
      case mpr =>
        intro h; rw [h]
      case mp =>
        intro h
        rw [(neg_neg (x := x)).symm, (neg_neg (x := y)).symm, h]

    @[simp]
    theorem add_left_cancel {c x y : ℤ ⧸ m} : c + x = c + y ↔ x = y := by
      constructor
      case mpr =>
        intro h; rw [h]
      case mp =>
        intro h
        calc x
          _ = (-c + c) + x  := by simp
          _ = -c + (c + x)  := by rw [← add_assoc]
          _ = -c + (c + y)  := by rw [h]
          _ = y             := by simp
    @[simp]
    theorem add_right_cancel {c x y : ℤ ⧸ m} : x + c = y + c ↔ x = y := by
      repeat rw [add_comm _ c]
      exact add_left_cancel
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



  /- SECTION: Multiplication and negation -/
  namespace arith
    @[simp]
    theorem mul_neg_one {m : ℤ} {x : ℤ ⧸ m} : x * (-1) = -x := by
      have : x * -1 + x = 0 := calc x * -1 + x
        _ = x * -1 + x * 1 := by simp
        _ = x * (-1 + 1) := by rw [mul_add]
        _ = 0 := by simp
      calc x * -1
        _ = x * -1 + 0 := by simp
        _ = x * -1 + (x + -x) := by simp
        _ = x * -1 + x + -x := by rw [add_assoc]
        _ = 0 + -x := by rw [this]
        _ = -x := by simp
    @[simp]
    theorem neg_one_mul {m : ℤ} {x : ℤ ⧸ m} : (-1) * x = -x := by
      rw [mul_comm] ; exact mul_neg_one

    @[simp]
    theorem neg_mul {m : ℤ} {x y : ℤ ⧸ m} : -x * y = - (x * y) := by
      apply Eq.symm
      have : x * y + -x * y = 0 := by
        rw [← add_mul]
        simp
      calc - (x * y)
        _ = - (x * y) + 0 := by simp
        _ = - (x * y) + (x * y + -x * y) := by rw [this]
        _ = -x * y := by simp
    @[simp]
    theorem mul_neg {m : ℤ} {x y : ℤ ⧸ m} : x * -y = - (x * y) := by
      rw [mul_comm]
      simp
      rw [mul_comm]
    @[simp]
    theorem neg_mul_neg {m : ℤ} {x y : ℤ ⧸ m} : (-x) * (-y) = x * y := by simp

    -- idk where to put this one really
    theorem neg_eq_comm {x y : ℤ ⧸ m} : -x = y ↔ -y = x := by
      constructor
      <;> (intro h; rw [h.symm, neg_neg])

  end arith



  /- SECTION: Subtraction -/
  def sub {m : ℤ} (x y : ℤ ⧸ m) : ℤ ⧸ m := x + -y
  instance instSub {m : ℤ} : Sub (ℤ ⧸ m) where sub := ℤMod.sub
  namespace arith
    /-- Defining property -/
    @[simp]
    theorem sub_eq_add_neg {x y : ℤ ⧸ m} : x - y = x + -y := rfl

    /-- Not a defining property -/
    theorem sub_mk {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) - ℤMod.mk y = ℤMod.mk (x - y) := by
      simp [neg_mk, add_mk, ℤ.results.ring.sub_eq_add_neg]

    @[simp]
    theorem sub_self {x : ℤ ⧸ m} : x - x = 0 := by simp
    @[simp]
    theorem sub_neg {x y : ℤ ⧸ m} : x - -y = x + y := by simp

    @[simp]
    theorem zero_sub {x : ℤ ⧸ m} : 0 - x = -x := by simp
    @[simp]
    theorem sub_zero {x : ℤ ⧸ m} : x - 0 = x := by simp
    @[simp]
    theorem neg_sub {x y : ℤ ⧸ m} : - (x - y) = y - x := by simp [add_comm]

    theorem eq_of_sub_eq_zero {x y : ℤ ⧸ m} : x - y = 0 → x = y := by
      simp
      intro h
      calc x
        _ = x + (-y + y)  := by simp
        _ = x + -y + y    := by rw [add_assoc]
        _ = y             := by simp [h]

    theorem add_sub_assoc {x y z : ℤ ⧸ m} : x + (y - z) = x + y - z := by simp
    theorem sub_add {x y z : ℤ ⧸ m} : x - (y + z) = x - y - z := by simp

    @[simp]
    theorem mul_sub {x y z : ℤ ⧸ m} : x * (y - z) = x * y - x * z := by simp
    @[simp]
    theorem sub_mul {x y z : ℤ ⧸ m} : (x - y) * z = x * z - y * z := by simp
  end arith



  /- SECTION: Arithmetic homs re. coersion `ℕ → ℤ → ℤ ⧸ m`: +, (- ·), *, (· - ·) -/
  namespace coe
    theorem fromℤ_add_hom {m x y : ℤ} : ((x + y : ℤ) : ℤ ⧸ m) = (x : ℤ ⧸ m) + (y : ℤ ⧸ m) := rfl
    theorem fromℤ_mul_hom {m x y : ℤ} : ((x * y : ℤ) : ℤ ⧸ m) = (x : ℤ ⧸ m) * (y : ℤ ⧸ m) := rfl

    theorem fromℕ_add_hom {m : ℤ} {x y : ℕ} : ((x + y : ℕ) : ℤ ⧸ m) = (x : ℤ ⧸ m) + (y : ℤ ⧸ m) := rfl
    theorem fromℕ_mul_hom {m : ℤ} {x y : ℕ} : ((x * y : ℕ) : ℤ ⧸ m) = (x : ℤ ⧸ m) * (y : ℤ ⧸ m) := by
      show ℤMod.mk (ℤ.mk (x * y, 0)) = ℤMod.mk (ℤ.mk (x, 0)) * ℤMod.mk (ℤ.mk (y, 0))
      rw [ℤ.results.coe_ℕ.coe_ℕ_hom_mul]
      rfl
  end coe



  /- SECTION: ⟦x⟧ = 0 ↔ m ∣ x and its special case ⟦m⟧ = 0 -/
  namespace arith
    theorem eq_zero_iff_multiple {x : ℤ} : (x : ℤ ⧸ m) = (0 : ℤ ⧸ m) ↔ m ∣ x := by
      rw  [ ←ntn_zero
          , ←ℤMod.quotax  -- good foresight to make a version of the induction axioms as a rewrite rule
          , same_remainder
          , ℤ.results.ring.zero_sub
          , ℤ.results.number_theory.divides_iff_divides_neg]

    @[simp]
    theorem modulus_eq_zero {m : ℤ} : (m : ℤ ⧸ m) = (0 : ℤ ⧸ m) := by
      rw [eq_zero_iff_multiple]
      exact ℤ.results.number_theory.divides_refl m
  end arith



  /- SECTION: Specialised field results modulo a *prime* -/
  section da_field

  namespace arith
    /-- NOTE: This proof is disgusting. It would be a lot more cleaner if I had developed the theory of `ℤ` a bit better first. -/
    theorem nonzero_invertible_mod_prime
      {p : ℕ} (h_p_prime : (p : ℤ).prime)
      (x : ℤ ⧸ p) (h_x_ne_zero : x ≠ 0)
      : ∃ (y : ℤ ⧸ p), x * y = 1
      := by
        have : p ≠ 0 := by
          intro h_p_eq_0
          rw [‹p = 0›, ℤ.ntn_zero] at h_p_prime
          have : (0 : ℤ) > 1 := h_p_prime.left
          rw [gt_iff_lt, ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub, ←ℤ.ntn_one, ℤ.results.ring.neg_mk] at this
          have ⟨a, h_a, h_a_ne_0⟩ := this
          have h_a := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
          contradiction -- `a = 0` and `a ≠ 0`
        have ⟨r, h_r, h_r_lt_p⟩ := x.existsCanonRep ‹p ≠ 0›
        have h_r_ne_0 : r ≠ 0 := by
          intro h_r_eq_0
          rw [h_r_eq_0, ℤ.ntn_zero, ntn_zero] at h_r
          contradiction -- `x = 0` and `x ≠ 0`
        have h_r_gt_0 : (r : ℤ) > 0 := by
          rw [gt_iff_lt, ℤ.results.ordered_ring.lt_mk]
          exists r
        have h_r_cop_p : (r : ℤ).coprime p := by
          intro d h_d_div_r h_d_div_p
          have ⟨u, h_u_inv, h_du⟩ := h_p_prime.right h_d_div_p
          cases h_du
          case inr h_du =>
            rw [h_du]
            assumption
          case inl h_du =>
            have : (p : ℤ) ∣ r := by
              have ⟨q, h_q⟩ := h_d_div_r
              exists q * u
              rw [h_q, h_du, ℤ.results.ring.spec.mul_assoc, ℤ.results.ring.mul_right_comm]
            have := ℤ.results.number_theory.le_of_divides ‹(r : ℤ) > 0› ‹(p : ℤ) ∣ r›
            have := ℤ.results.coe_ℕ.coe_ℕ_hom_lt.mp h_r_lt_p
            have ⟨a, h_a⟩ := ‹(p : ℤ) ≤ r›
            rw [ℤ.results.ordered_ring.lt_mk] at this
            have ⟨b, h_b, h_b_ne_0⟩ := this
            have : ℤ.mk (0, b) = ℤ.mk (a, 0) := calc ℤ.mk (0, b)
              _ = - ℤ.mk (b, 0)                   := by rw [ℤ.results.ring.neg_mk]
              _ = - (ℤ.mk (p, 0) - ℤ.mk (r, 0))   := by rw [← h_b]
              _ = ℤ.mk (r, 0) - ℤ.mk (p, 0)       := by
                rw  [ ℤ.results.ring.sub_eq_add_neg, ℤ.results.ring.neg_add'
                    , ℤ.results.ring.neg_neg
                    , ℤ.results.ring.add_comm
                    , ℤ.results.ring.sub_eq_add_neg]
              _ = ℤ.mk (a, 0)                     := by rw [h_a]
            have : b = 0 := this |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.right
            contradiction -- `b = 0` and `b ≠ 0`
        have ⟨a, b, h_ab⟩ := ℤ.results.number_theory.bezout ‹(r : ℤ).coprime p›
        have h_ab : mk r * mk a + mk p * mk b = (1 : ℤ ⧸ p) := by
          rw  [← ntn_one
              , mul_mk, mul_mk
              , add_mk
              , h_ab]
        exists a
        have : x * a = 1 := calc x * ℤMod.mk a
          _ = x * a + p * b := by simp
          _ = r * a + p * b := by simp [h_r]
          _ = 1 := by
            show mk (ℤ.mk (r, 0)) * mk a + mk (ℤ.mk (p, 0)) * mk b = 1
            rw [h_ab]
        assumption
  end arith

  /-- NOTE: This could've been a computable function if I had properly done the extended Euclidean algorithm. -/
  noncomputable
  def inv {p : ℕ} {_ : (p : ℤ).prime} (x : ℤ ⧸ p) {_ : x ≠ 0} : ℤ ⧸ p := Classical.choose <| arith.nonzero_invertible_mod_prime ‹(p : ℤ).prime› x ‹x ≠ 0›
  def inv_spec {p : ℕ} {_ : (p : ℤ).prime} (x : ℤ ⧸ p) {_ : x ≠ 0} : x * (@inv p (by assumption) x (by assumption)) = 1 := Classical.choose_spec <| arith.nonzero_invertible_mod_prime ‹(p : ℤ).prime› x ‹x ≠ 0›

  notation:max x "⁻¹" => @inv _ (by assumption) x (by assumption) -- this is kinda a hack...

  namespace arith
    -- NOTE: Field axiom
    theorem zero_ne_one {_ : (p : ℤ).prime} : (0 : ℤ ⧸ p) ≠ (1 : ℤ ⧸ p) := by
      rw [← ntn_zero, ← ntn_one]
      intro h_0_eq_q
      have : (p : ℤ) ∣ 1 - 0 := h_0_eq_q |> ℤMod.exact
      have : (p : ℤ) ∣ 1 := by rw [ℤ.results.ring.sub_zero] at this ; assumption
      have := ℤ.results.number_theory.unit_of_divides_unit ℤ.results.ring.one_invertible this |> ℤ.results.ring.solve_invertible
      cases this
      case inl h_p_eq_1 =>
        have := ‹(p : ℤ).prime›.left
        rw [h_p_eq_1, gt_iff_lt] at this
        have := ℤ.results.ordered_ring.lt_irrefl 1
        contradiction -- `1 < 1` and `¬ (1 < 1)`
      case inr h_p_eq_neg_1 =>
        have := ‹(p : ℤ).prime›.left
        rw [h_p_eq_neg_1, gt_iff_lt, ℤ.results.ordered_ring.lt_mk] at this
        have ⟨a, h_a, h_a_ne_0⟩ := this
        rw [← ℤ.ntn_one, ℤ.results.ring.neg_mk, ℤ.results.ring.sub_mk] at h_a
        have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
        contradiction -- `a = 0` and `a ≠ 0`
    -- NOTE: Field axiom
    @[simp]
    theorem mul_inv {p : ℕ} {_ : (p : ℤ).prime} {x : ℤ ⧸ p} {_ : x ≠ 0} : x * x⁻¹ = (1 : ℤ ⧸ p) := @inv_spec p ‹(p : ℤ).prime› x ‹x ≠ 0›
    -- NOTE: Field axiom
    @[simp]
    theorem inv_mul {p : ℕ} {_ : (p : ℤ).prime} {x : ℤ ⧸ p} {_ : x ≠ 0} : x⁻¹ * x = (1 : ℤ ⧸ p) := by
      rw [mul_comm]
      exact mul_inv

    theorem null_factor {p : ℕ} {_ : (p : ℤ).prime} {x y : ℤ ⧸ p} : x * y = 0 ↔ x = 0 ∨ y = 0 := by
      constructor
      case mpr =>
        intro h ; cases h
        <;> (rename_i h ; simp [h])
      case mp =>
        intro h
        apply Classical.byContradiction
        rw [not_or, ←ne_eq, ←ne_eq]
        intro ⟨_, _⟩
        have : y = 0 := calc y
          _ = x⁻¹ * (x * y) := by simp
          _ = x⁻¹ * 0       := by rw [h]
          _ = 0             := by rw [mul_zero]
        contradiction -- `y = 0` and `y ≠ 0`

    theorem null_factor_divisibility {p : ℕ} {_ : (p : ℤ).prime} {x y : ℤ} : p ∣ (x * y) ↔ (p ∣ x) ∨ (p ∣ y) := by
      repeat rw [←eq_zero_iff_multiple]
      rw [coe.fromℤ_mul_hom]
      exact @null_factor p ‹(p : ℤ).prime› (x := mk x) (y := mk y)
  end arith
  end da_field

end ℤMod

end Numbers
