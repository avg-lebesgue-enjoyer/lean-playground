/- @file LeanPlayground/Numbers/Results/Integer.lean
 - Results proven about the integers ℤ.
 -/

/- IMPORTS: ℤ -/
import LeanPlayground.Numbers.Integer
import LeanPlayground.Numbers.Results.Natural



/- LAUNCH: Results -/

namespace Numbers.ℤ.results
  -- SECTION: Induction/universal-property/pattern-matching principles
  /-- The somewhat trivial part of the quotient axiomitisation for `ℤ`. -/
  theorem ℤ.exact {p q : ℕ × ℕ} : ℤ.mk p = ℤ.mk q → p ≈ q := Numbers.ℤ.exact

  /-- The nontrivial part of the quotient axiomitisation for `ℤ`. -/
  theorem ℤ.sound {p q : ℕ × ℕ} : p ≈ q → ℤ.mk p = ℤ.mk q := Numbers.ℤ.sound

  /--
    The induction principle for `ℤ`: every element may as well be of the form `ℤ.mk (something : ℕ × ℕ)`.

    For more extensive documentation, see `ℤ.indOn`
  -/
  theorem ℤ.ind {β : ℤ → Prop} (mk : ∀ (p : ℕ × ℕ), β (ℤ.mk p)) : (z : ℤ) → β z := Numbers.ℤ.ind mk

  /--
    "Pattern-matching" the provided argument as `ℤ.mk (something : ℕ × ℕ)`. See also `ℤ.ind`.

    A common mnemonic to use in tactic mode is `apply ℤ.indOn x ; intro (a, b)` which "grabs a
      representative pair `(a, b)` for `x`", in the sense that it replaces `x` with `ℤ.mk (a, b)`.
    Alternatively, one can think of this as "pattern-matching" `x` with the "constructor"-based
      pattern `ℤ.mk (a, b)`. Thought of in this way, this mnemonic should be used any time you want
      to write `let ℤ.mk (a, b) := x` or `match x with | ℤ.mk (a, b) =>` etc.
   -/
  theorem ℤ.indOn {β : ℤ → Prop} (z : ℤ) (mk : ∀ (p : ℕ × ℕ), β (ℤ.mk p)) : β z := Numbers.ℤ.indOn z mk

  /-- Existence form of `ℤ.indOn`. -/
  theorem ℤ.existsRep (z : ℤ) : ∃ (a b : ℕ), z = ℤ.mk (a, b) := Numbers.ℤ.existsRep z

  /-- "Nonnegative or nonpositive" representatives in `ℤ`. -/
  theorem ℤ.existsCanonRep (z : ℤ) : ∃ (n : ℕ), z = ℤ.mk (n, 0) ∨ z = ℤ.mk (0, n) := Numbers.ℤ.existsCanonRep z


  -- SECTION: Notation
  /-- The canonical quotient map for `ℤ := ℕ × ℕ ⧸ same_difference`. -/
  def ℤ.mk : ℕ × ℕ → ℤ := Numbers.ℤ.mk
  theorem add_ntn {x y : ℤ} : x.add y = x + y := rfl
  theorem mul_ntn {x y : ℤ} : x.mul y = x * y := rfl
  theorem le_ntn {x y : ℤ} : x.le y = (x ≤ y) := rfl
  theorem lt_ntn {x y : ℤ} : x.lt y = (x < y) := rfl



  -- SECTION: Coersion `ℕ ↪ ℤ`
  instance : Coe ℕ ℤ where coe := Numbers.ℤ.coe_from_ℕ.it.coe



  -- SECTION: The ring `ℤ` of integers
  -- The commutative unital ring axioms
  namespace ring.spec
    open Numbers.ℤ
    -- Additive abelian group
    /-- Associativity of `ℤ.add`. -/
    theorem add_assoc {x y z : ℤ} : x + (y + z) = (x + y) + z := arith.add_assoc
    /-- Commutativity of `ℤ.add`. -/
    theorem add_comm (x y : ℤ) : x + y = y + x := arith.add_comm x y
    /-- Right-neutrality of `0` for `ℤ.add`. -/
    theorem add_zero (x : ℤ) : x + 0 = x := arith.add_zero
    /-- Left-neutrality of `0` for `ℤ.add`. -/
    theorem zero_add (x : ℤ) : 0 + x = x := arith.zero_add
    theorem add_neg {x : ℤ} : x + (-x) = 0 := arith.add_neg
    theorem neg_add {x : ℤ} : (-x) + x = 0 := arith.neg_add
    -- Multiplicative commutative monoid
    theorem mul_assoc {x y z : ℤ} : x * (y * z) = (x * y) * z := arith.mul_assoc
    theorem mul_comm (x y : ℤ) : x * y = y * x := arith.mul_comm x y
    theorem mul_one {x : ℤ} : x * 1 = x := arith.mul_one
    theorem one_mul {x : ℤ} : 1 * x = x := arith.one_mul
    -- Distributivity
    theorem mul_add {a x y : ℤ} : a * (x + y) = a * x + a * y := arith.mul_add
    theorem add_mul {a b x : ℤ} : (a + b) * x = a * x + b * x := arith.add_mul
  end ring.spec

  -- More results
  namespace ring
    open Numbers.ℤ

    -- `export` the stuff from `Numbers.ℤ.results.ring.spec` into `Numbers.ℤ.results.ring`
    export spec (add_assoc add_comm add_zero zero_add add_neg neg_add mul_assoc mul_comm mul_one one_mul mul_add add_mul)

    /-- The defining property of `ℤ.add`: it acts as pairwise addition on arguments of the form `ℤ.mk (thing : ℕ × ℕ)`. -/
    theorem add_mk {a b x y : ℕ} : (ℤ.mk (a, b)) + (ℤ.mk (x, y)) = ℤ.mk (a + x, b + y) := arith.add_mk
    /-- The defining property of `ℤ.neg`: it swaps the components of a `thing : ℕ × ℕ` when applied to `ℤ.mk thing`. -/
    theorem neg_mk {a b : ℕ} : - ℤ.mk (a, b) = ℤ.mk (b, a) := arith.neg_mk
    /-- The defining property of `ℤ.mul`: it does that stuff on arguments of the form `ℤ.mk (thing : ℕ × ℕ)`. -/
    theorem mul_mk {a b x y : ℕ} : (ℤ.mk (a, b)) * (ℤ.mk (x, y)) = ℤ.mk (a * x + b * y, a * y + b * x) := arith.mul_mk

    /-- My beloved <3, specialised to `ℤ`. (Note to self: Holds in any ring. Should generalise the proof...) -/
    theorem add_right_comm {x y : ℤ} (z : ℤ) : x + y + z = x + z + y := arith.add_right_comm z

    theorem neg_neg {x : ℤ} : -(-x) = x := arith.neg_neg
    /-- Sorry, I wanted to call this `neg_add`, but I've already given that name to a more important result... -/
    theorem neg_add' {x y : ℤ} : - (x + y) = -x + -y := arith.neg_add'
    theorem neg_zero : -(0 : ℤ) = 0 := arith.neg_zero

    /-- The defining equation for `ℤ.sub`. -/
    theorem sub_eq_add_neg {x y : ℤ} : x - y = x + -y := arith.sub_eq_add_neg
    theorem sub_self {x : ℤ} : x - x = 0 := arith.sub_self
    theorem sub_neg {x y : ℤ} : x - -y = x + y := arith.sub_neg
    theorem neg_sub {x y : ℤ} : - (x + y) = -x - y := arith.neg_sub
    theorem zero_sub {x : ℤ} : 0 - x = -x := arith.zero_sub
    theorem sub_zero {x : ℤ} : x - 0 = x := arith.sub_zero
    theorem swap_sub {x y : ℤ} : - (x - y) = y - x := arith.swap_sub

    theorem eq_of_sub_eq_zero {x y : ℤ} : x - y = 0 → x = y := arith.eq_of_sub_eq_zero
    theorem add_sub_assoc {x y z : ℤ} : x + (y - z) = x + y - z := arith.add_sub_assoc
    theorem sub_add {x y z : ℤ} : x - (y + z) = x - y - z := arith.sub_add

    theorem mul_zero {x : ℤ} : x * 0 = 0 := arith.mul_zero
    theorem zero_mul {x : ℤ} : 0 * x = 0 := arith.zero_mul

    theorem mul_neg_one {x : ℤ} : x * (-1) = -x := arith.mul_neg_1
    theorem neg_one_mul {x : ℤ} : (-1) * x = -x := arith.neg_1_mul

    theorem mul_sub {a x y : ℤ} : a * (x - y) = a * x - a * y := arith.mul_sub
    theorem sub_mul {a b x : ℤ} : (a - b) * x = a * x - b * x := arith.sub_mul

    theorem neg_mul {x y : ℤ} : - (x * y) = -x * y := arith.neg_mul
    theorem neg_mul_right {x y : ℤ} : - (x * y) = x * -y := arith.neg_mul_right
    theorem neg_mul_neg {x y : ℤ} : (-x) * (-y) = x * y := arith.neg_mul_neg

    theorem eq_iff_sub_eq_zero {x y : ℤ} : x - y = 0 ↔ x = y := arith.eq_iff_sub_eq_zero

    theorem neg_eq_comm {x y : ℤ} : -x = y ↔ -y = x := arith.neg_eq_comm

    /-- The null factor law; see also `null_factor`. -/
    theorem mul_eq_zero {x y : ℤ} : x * y = 0 ↔ x = 0 ∨ y = 0 := arith.mul_eq_zero
    /-- Alternative name for `ℤ.arith.mul_eq_zero`. -/
    theorem null_factor {x y : ℤ} : x * y = 0 ↔ x = 0 ∨ y = 0 := arith.null_factor

    theorem mul_ne_zero
      {x y : ℤ}
      : x ≠ 0
      → y ≠ 0
      → x * y ≠ 0
      := arith.mul_ne_zero

    theorem add_left_cancel
      {c x y : ℤ}
      : c + x = c + y
      → x = y
      := arith.add_left_cancel
    theorem add_right_cancel
      {c x y : ℤ}
      : x + c = y + c
      → x = y
      := arith.add_right_cancel
    theorem mul_left_cancel
      {c x y : ℤ}
      : c ≠ 0
      → c * x = c * y
      → x = y
      := arith.mul_left_cancel
    theorem mul_right_cancel
      {c x y : ℤ}
      : c ≠ 0
      → x * c = y * c
      → x = y
      := arith.mul_right_cancel

    theorem mul_right_comm
      {x y : ℤ} (z : ℤ)
      : x * y * z = x * z * y
      := arith.mul_right_comm z

    theorem zero_ne_one : (0 : ℤ) ≠ (1 : ℤ) := arith.zero_ne_one
    theorem one_ne_neg_one : (1 : ℤ) ≠ (-1 : ℤ) := arith.one_ne_neg_one

    theorem one_invertible : ℤ.invertible 1 := arith.one_invertible
    theorem neg_one_invertible : ℤ.invertible (-1) := arith.neg_one_invertible

    theorem invertible_of_mul_one {x y : ℤ} : x * y = 1 → x.invertible ∧ y.invertible := arith.invertible_of_mul_one
    theorem ne_zero_of_invertible {x : ℤ} : x.invertible → x ≠ 0 := arith.ne_zero_of_invertible
    theorem mul_invertible {x y : ℤ} : invertible x → invertible y → invertible (x * y) := arith.mul_invertible
    theorem invertible_of_mul_invertible
      {x y : ℤ}
      : invertible (x * y)
      → invertible x ∧ invertible y
      := arith.invertible_of_mul_invertible

    theorem solve_invertible
      {x : ℤ}
      : x.invertible
      → x = 1 ∨ x = -1
      := arith.solve_invertible
    theorem solve_mul_eq_one
      {x y : ℤ}
      : x * y = 1
      → (x = 1 ∧ y = 1)
        ∨ (x = -1 ∧ y = -1)
      := arith.solve_mul_eq_one

    -- More results will come to mind as they prove useful
  end ring



  -- SECTION: The orders `<` and `≤` on `ℤ`
  namespace ordered_ring
    /-- Defining property of `ℤ.le`. -/
    theorem le_mk {x y : ℤ} : x ≤ y ↔ ∃ (a : ℕ), y - x = ℤ.mk (a, 0) := order.le_mk

    theorem le_refl (x : ℤ) : x ≤ x := order.le_refl x
    theorem le_antisymm {x y : ℤ} : x ≤ y → y ≤ x → x = y := order.le_antisymm
    theorem le_trans {x y z : ℤ} : x ≤ y → y ≤ z → x ≤ z := order.le_trans

    theorem le_add_hom {a b x y : ℤ} : a ≤ b → x ≤ y → a + x ≤ b + y := order.le_add_hom
    theorem le_neg_antihom {x y : ℤ} : x ≤ y → -y ≤ -x := order.le_neg_antihom

    theorem le_of_nat {x : ℕ} : (0 : ℤ) ≤ (x : ℤ) := order.le_of_nat

    /-- Defining property of `ℤ.lt`. -/
    theorem lt_iff_le_and_ne {x y : ℤ} : x < y ↔ x ≤ y ∧ x ≠ y := order.lt_iff_le_and_ne
    theorem le_iff_lt_or_eq {x y : ℤ} : x ≤ y ↔ x < y ∨ x = y := order.le_iff_lt_or_eq
    theorem lt_iff_not_ge {x y : ℤ} : x < y ↔ ¬ (x ≥ y) := order.lt_iff_not_ge

    theorem le_or_eq_iff_le {x y : ℤ} : x ≤ y ∨ x = y ↔ x ≤ y := order.le_or_eq_iff_le

    theorem lt_irrefl (x : ℤ) : ¬ (x < x) := order.lt_irrefl x
    theorem lt_asymm {x y : ℤ} : x < y → ¬ (y < x) := order.lt_asymm
    theorem lt_trans {x y z : ℤ} : x < y → y < z → x < z := order.lt_trans

    /-- Not actually the defining relationship for `ℤ.lt`. -/
    theorem lt_mk {x y : ℤ} : x < y ↔ ∃ (a : ℕ), y - x = ℤ.mk (a, 0) ∧ a ≠ 0 := order.lt_mk

    /-- The trichotomous (total order) property of `ℤ.lt`. -/
    theorem lt_trichotomy (x y : ℤ) : x < y ∨ x = y ∨ y < x := order.lt_trichotomy x y

    theorem sub_le {x y z : ℤ} : x - y ≤ z ↔ x ≤ z + y := order.sub_le
    theorem le_sub {x y z : ℤ} : x ≤ y - z ↔ x + z ≤ y := order.le_sub
    theorem sub_lt {x y z : ℤ} : x - y < z ↔ x < z + y := order.sub_lt
    theorem lt_sub {x y z : ℤ} : x < y - z ↔ x + z < y := order.lt_sub

    theorem lt_iff_le_sub_one {x y : ℤ} : x < y ↔ x ≤ y - 1 := order.lt_iff_le_sub_one
    theorem nonneg_of_mul_nonneg {x y : ℤ} : 0 ≤ x → 0 ≤ y → 0 ≤ x * y := order.nonneg_of_mul_nonneg
    theorem le_iff_sub_nonneg {x y : ℤ} : x ≤ y ↔ 0 ≤ y - x := order.le_iff_sub_nonneg
  end ordered_ring



  -- SECTION: Basic number theory
  namespace number_theory
    theorem divides_refl (x : ℤ) : x ∣ x := divisibility.divides_refl x
    theorem divides_antisymm {x y : ℤ} : x ∣ y → y ∣ x → x = y ∨ x = -y := divisibility.divides_antisymm
    theorem divides_trans {x y z : ℤ} : x ∣ y → y ∣ z → x ∣ z := divisibility.divides_trans
    theorem le_of_divides {d x : ℤ} : x > 0 → d ∣ x → d ≤ x := divisibility.le_of_divides
  end number_theory -- thank heavens



  /- SECTION: Results yet to be proven
    [3.] Euclidean division and Bezout's lemma
      Primality (include respecting `ℕ.prime` along `ℕ ↪ ℤ`)
      Euclidean division (include respecting `ℕ.euclidean_division` along `ℕ ↪ ℤ`)
      `gcd`
      Bezout's lemma
      (After this is done, move to a new file `Modular.lean` and start reasoning about `ℤ ⧸ n`; goal is still fund. arith.)
  -/


end Numbers.ℤ.results
