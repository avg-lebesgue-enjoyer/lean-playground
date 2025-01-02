/- @file LeanPlayground/Numbers/Modular.lean
 - Results concerning the theory of `ℤ ⧸ m` for `m : ℤ`.
 -/

/- IMPORTS: All -/
import LeanPlayground.Numbers.Results.Natural
import LeanPlayground.Numbers.Results.Integer
import LeanPlayground.Numbers.Modular



/- LAUNCH: Results -/

namespace Numbers.Modular.results
  -- SECTION: Induction/universal-property/pattern-matching principles
  @[inherit_doc Numbers.ℤMod.exact]
  theorem ℤMod.exact {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk y → same_remainder m x y := Numbers.ℤMod.exact
  @[inherit_doc Numbers.ℤMod.sound]
  theorem ℤMod.sound {m x y : ℤ} : same_remainder m x y → (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk y := Numbers.ℤMod.sound
  @[inherit_doc Numbers.ℤMod.quotax]
  theorem ℤMod.quotax {m x y : ℤ} : same_remainder m x y ↔ (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk y := Numbers.ℤMod.quotax
  @[inherit_doc Numbers.ℤMod.ind]
  theorem ℤMod.ind {m : ℤ} {β : (ℤ ⧸ m) → Prop} (mk : ∀ (z : ℤ), β (ℤMod.mk z)) : (a : ℤ ⧸ m) → β a := Numbers.ℤMod.ind mk
  @[inherit_doc Numbers.ℤMod.indOn]
  theorem ℤMod.indOn {m : ℤ} (a : ℤ ⧸ m) {β : (ℤ ⧸ m) → Prop} (mk : ∀ (z : ℤ), β (ℤMod.mk z)) : β a := Numbers.ℤMod.indOn a mk
  @[inherit_doc Numbers.ℤMod.existsRep]
  theorem ℤMod.existsRep {m : ℤ} (a : ℤ ⧸ m) : ∃ (z : ℤ), a = ℤMod.mk z := Numbers.ℤMod.existsRep a
  @[inherit_doc Numbers.ℤMod.existsCanonRep]
  theorem ℤMod.existsCanonRep {n : ℕ} (h_n_ne_zero : n ≠ 0) (a : ℤ ⧸ n) : ∃ (r : ℕ), a = ℤMod.mk r ∧ r < n := Numbers.ℤMod.existsCanonRep h_n_ne_zero a
  @[inherit_doc Numbers.ℤMod.lift]
  def ℤMod.lift {m : ℤ} {β : Sort u} (f : ℤ → β) : (∀ (x y : ℤ), same_remainder m x y → f x = f y) → (ℤ ⧸ m) → β := Numbers.ℤMod.lift f


  -- SECTION: Notation / Defining Rules / virtually-defining rules
  theorem ntn_zero {m : ℤ} : (ℤMod.mk 0 : ℤ ⧸ m) = 0 := ℤMod.ntn_zero
  theorem ntn_one {m : ℤ} : (ℤMod.mk 1 : ℤ ⧸ m) = 1 := ℤMod.ntn_one
  theorem add_mk {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) + (ℤMod.mk y) = ℤMod.mk (x + y) := ℤMod.arith.add_mk
  theorem neg_mk {m x : ℤ} : - (ℤMod.mk x : ℤ ⧸ m) = ℤMod.mk (-x) := ℤMod.arith.neg_mk
  theorem mul_mk {m x y : ℤ} : (ℤMod.mk x : ℤ ⧸ m) * (ℤMod.mk y) = ℤMod.mk (x * y) := ℤMod.arith.mul_mk



  -- SECTION: Coercion `ℤ → ℤ ⧸ n`



  -- SECTION: Coercion `ℕ ↪ ℤ ⧸ n`



  -- SECTION: The ring `ℤ` of integers modulo a thing
  -- The commutative unital ring axioms
  namespace ring.spec
    open Numbers.ℤMod
    -- Additive abelian group
    theorem add_assoc {m : ℤ} {x y z : ℤ ⧸ m} : x + (y + z) = (x + y) + z := arith.add_assoc
    theorem add_comm {m : ℤ} (x y : ℤ ⧸ m) : x + y = y + x := arith.add_comm x y
    theorem add_zero {m : ℤ} {x : ℤ ⧸ m} : x + 0 = x := arith.add_zero
    theorem zero_add {m : ℤ} {x : ℤ ⧸ m} : 0 + x = x := arith.zero_add
    theorem add_neg {m : ℤ} {x : ℤ ⧸ m} : x + -x = 0 := arith.add_neg
    theorem neg_add {m : ℤ} {x : ℤ ⧸ m} : -x + x = 0 := arith.neg_add
    -- Multiplicative commutative monoid
    theorem mul_assoc {m : ℤ} {x y z : ℤ ⧸ m} : x * (y * z) = (x * y) * z := arith.mul_assoc
    theorem mul_comm {m : ℤ} (x y : ℤ ⧸ m) : x * y = y * x := arith.mul_comm x y
    theorem mul_one {m : ℤ} {x : ℤ ⧸ m} : x * 1 = x := arith.mul_one
    theorem one_mul {m : ℤ} {x : ℤ ⧸ m} : 1 * x = x := arith.one_mul
    -- -- Distributivity
    -- theorem mul_add {a x y : ℤ} : a * (x + y) = a * x + a * y := arith.mul_add
    -- theorem add_mul {a b x : ℤ} : (a + b) * x = a * x + b * x := arith.add_mul
  end ring.spec

  -- More results
  namespace ring
    open Numbers.ℤMod
    -- `export` the stuff from `Numbers.ℤ.results.ring.spec` into `Numbers.ℤ.results.ring`
    -- export spec (add_assoc add_comm add_zero zero_add add_neg neg_add mul_assoc mul_comm mul_one one_mul mul_add add_mul)

    -- /-- The defining property of `ℤ.mul`: it does that stuff on arguments of the form `ℤ.mk (thing : ℕ × ℕ)`. -/
    -- theorem mul_mk {a b x y : ℕ} : (ℤ.mk (a, b)) * (ℤ.mk (x, y)) = ℤ.mk (a * x + b * y, a * y + b * x) := arith.mul_mk
    -- /-- Not a defining property, but super useful. -/
    -- theorem sub_mk {a b x y : ℕ} : mk (a, b) - mk (x, y) = mk (a + y, b + x) := arith.sub_mk

    /-- My beloved <3, specialised to `ℤ`. (Note to self: Holds in any ring. Should generalise the proof...) -/
    theorem add_right_comm {m : ℤ} {x y : ℤ ⧸ m} (z : ℤ ⧸ m) : x + y + z = x + z + y := arith.add_right_comm z

    theorem neg_neg {m : ℤ} {x : ℤ ⧸ m} : - - x = x := arith.neg_neg
    -- /-- Sorry, I wanted to call this `neg_add`, but I've already given that name to a more important result... -/
    theorem neg_add' {m : ℤ} {x y : ℤ ⧸ m} : - (x + y) = -x + -y := arith.neg_add'
    theorem neg_zero {m : ℤ} : - (0 : ℤ ⧸ m) = 0 := arith.neg_zero

    -- /-- The defining equation for `ℤ.sub`. -/
    -- theorem sub_eq_add_neg {x y : ℤ} : x - y = x + -y := arith.sub_eq_add_neg
    -- theorem sub_self {x : ℤ} : x - x = 0 := arith.sub_self
    -- theorem sub_neg {x y : ℤ} : x - -y = x + y := arith.sub_neg
    -- theorem neg_sub {x y : ℤ} : - (x + y) = -x - y := arith.neg_sub
    -- theorem zero_sub {x : ℤ} : 0 - x = -x := arith.zero_sub
    -- theorem sub_zero {x : ℤ} : x - 0 = x := arith.sub_zero
    -- theorem swap_sub {x y : ℤ} : - (x - y) = y - x := arith.swap_sub

    -- theorem eq_of_sub_eq_zero {x y : ℤ} : x - y = 0 → x = y := arith.eq_of_sub_eq_zero
    -- theorem add_sub_assoc {x y z : ℤ} : x + (y - z) = x + y - z := arith.add_sub_assoc
    -- theorem sub_add {x y z : ℤ} : x - (y + z) = x - y - z := arith.sub_add

    -- theorem mul_zero {x : ℤ} : x * 0 = 0 := arith.mul_zero
    -- theorem zero_mul {x : ℤ} : 0 * x = 0 := arith.zero_mul

    -- theorem mul_neg_one {x : ℤ} : x * (-1) = -x := arith.mul_neg_1
    -- theorem neg_one_mul {x : ℤ} : (-1) * x = -x := arith.neg_1_mul

    -- theorem mul_sub {a x y : ℤ} : a * (x - y) = a * x - a * y := arith.mul_sub
    -- theorem sub_mul {a b x : ℤ} : (a - b) * x = a * x - b * x := arith.sub_mul

    -- theorem neg_mul {x y : ℤ} : - (x * y) = -x * y := arith.neg_mul
    -- theorem neg_mul_right {x y : ℤ} : - (x * y) = x * -y := arith.neg_mul_right
    -- theorem neg_mul_neg {x y : ℤ} : (-x) * (-y) = x * y := arith.neg_mul_neg

    -- theorem eq_iff_sub_eq_zero {x y : ℤ} : x - y = 0 ↔ x = y := arith.eq_iff_sub_eq_zero

    -- theorem neg_eq_comm {x y : ℤ} : -x = y ↔ -y = x := arith.neg_eq_comm

    -- theorem add_left_cancel {c x y : ℤ} : c + x = c + y → x = y := arith.add_left_cancel
    -- theorem add_right_cancel {c x y : ℤ} : x + c = y + c → x = y := arith.add_right_cancel

    theorem mul_right_comm {m : ℤ} {x y : ℤ ⧸ m} (z : ℤ ⧸ m) : x * y * z = x * z * y := arith.mul_right_comm z

    -- theorem neg_inj {x y : ℤ} : -x = -y ↔ x = y := arith.neg_inj
    -- theorem neg_zero_eq_zero : - (0 : ℤ) = (0 : ℤ) := arith.neg_zero_eq_zero
  end ring



  -- SECTION: The field `ℤ ⧸ p` of integers modulo a prime
  -- The field axioms
  namespace field.spec
    -- `export` the stuff from `Numbers.ℤ.results.ring.spec` into `Numbers.ℤ.results.field.spec`
    -- export ring.spec (add_assoc add_comm add_zero zero_add add_neg neg_add mul_assoc mul_comm mul_one one_mul mul_add add_mul)
  end field.spec

  -- More results
  namespace field
    --
  end field



  /- SECTION: Results yet to be proven
    [1.] Ring results
      Prove everything that's there
    [2.] Field results
      Including and *especially* the null factor law.
      ^^ interpret this as `p ∣ (a * b) → p ∣ a ∨ p ∣ b` too
    [3.] Future horizons
      Move to a new file, called `FundArith.lean`, and prove that theorem
  -/

end Numbers.Modular.results
