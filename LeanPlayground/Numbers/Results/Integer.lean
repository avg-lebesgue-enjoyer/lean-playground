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


  -- SECTION: Notation
  /-- The canonical quotient map for `ℤ := ℕ × ℕ ⧸ same_difference`. -/
  def ℤ.mk : ℕ × ℕ → ℤ := Numbers.ℤ.mk



  -- SECTION: Coersion ℕ ↪ ℤ
  instance : Coe ℕ ℤ where coe := Numbers.ℤ.coe_from_ℕ.it.coe



  -- SECTION: The ring ℤ of integers
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
    theorem mul_assoc {x y z : ℤ} : x * (y * z) = (x * y) * z := sorry
    theorem mul_comm (x y : ℤ) : x * y = y * x := sorry
    theorem mul_one {x : ℤ} : x * 1 = x := sorry
    theorem one_mul {x : ℤ} : 1 * x = x := sorry
    -- Distributivity
    theorem mul_add {a x y : ℤ} : a * (x + y) = a * x + a * y := sorry
    theorem add_mul {a b x : ℤ} : (a + b) * x := a * x + b * x := sorry
  end ring.spec

  -- More results
  namespace ring
    open Numbers.ℤ

    -- `export` the stuff from `ring.spec` into `ring`
    export spec (add_assoc add_comm add_zero zero_add add_neg neg_add mul_assoc mul_comm mul_one one_mul mul_add add_mul)

    /-- The defining property of `ℤ.add`: it acts as pairwise addition on arguments of the form `ℤ.mk (thing : ℕ × ℕ)`. -/
    theorem add_mk {a b x y : ℕ} : (ℤ.mk (a, b)) + (ℤ.mk (x, y)) = ℤ.mk (a + x, b + y) := arith.add_mk
    /-- The defining property of `ℤ.neg`: it swaps the components of a `thing : ℕ × ℕ` when applied to `ℤ.mk thing`. -/
    theorem neg_mk {a b : ℕ} : - ℤ.mk (a, b) = ℤ.mk (b, a) := arith.neg_mk

    theorem neg_neg {x : ℤ} : -(-x) = x := arith.neg_neg

    theorem sub_eq_add_neg {x y : ℤ} : x - y = x + -y := sorry
    theorem sub_self {x : ℤ} : x - x = 0 := sorry
    theorem sub_neg {x y : ℤ} : x - -y = x + y := sorry
    theorem neg_sub {x y : ℤ} : - (x + y) = -x - y := sorry
    theorem neg_dist_add {x y : ℤ} : - (x + y) = -x + -y := sorry

    theorem mul_zero {x : ℤ} : x * 0 = 0 := sorry
    theorem zero_mul {x : ℤ} : 0 * x = 0 := sorry

    theorem mul_neg_1 {x : ℤ} : x * (-1) = -x := sorry
    theorem neg_1_mul {x : ℤ} : (-1) * x = -x := sorry

    -- More results will come to mind as they prove useful
  end ring


  /- SECTION: Results yet to be proven
    [1.] Ring ℤ
      Include subtraction
    [2.] Order
      Positive numbers
      `<` and `≤`
    [3.] Euclidean division and Bezout's lemma
      Primality (include respecting `ℕ.prime` along `ℕ ↪ ℤ`)
      Euclidean division (include respecting `ℕ.euclidean_division` along `ℕ ↪ ℤ`)
      `gcd`
      Bezout's lemma
      (After this is done, move to a new file `Modular.lean` and start reasoning about `ℤ ⧸ n`; goal is still fund. arith.)
  -/


end Numbers.ℤ.results
