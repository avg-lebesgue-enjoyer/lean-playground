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
/-- Existence form of `ℤ.indOn`. -/
theorem ℤ.existsRep (z : ℤ) : ∃ (a b : ℕ), z = ℤ.mk (a, b) := by
  apply z.indOn ; intro (a, b)
  exists a ; exists b
/-- "Nonnegative or nonpositive" representatives in `ℤ`. -/
theorem ℤ.existsCanonRep (z : ℤ) : ∃ (n : ℕ), z = ℤ.mk (n, 0) ∨ z = ℤ.mk (0, n) := by
  have ⟨a, b, h_ab⟩ := ℤ.existsRep z
  rw [h_ab]
  have h := ℕ.results.order.trichotomy a b
  cases h
  case inl h =>
    have ⟨δ, h_δ, h_δ_ne_0⟩ := h
    exists δ
    apply Or.inr
    apply ℤ.sound
    show a + δ = 0 + b
    rw [ℕ.results.arithmetic.zero_add, Eq.comm]
    assumption
  case inr h =>
    cases h
    case inl h =>
      exists 0
      apply Or.inl
      apply ℤ.sound
      show a + 0 = 0 + b
      rw [ℕ.results.arithmetic.add_zero, ℕ.results.arithmetic.zero_add]
      assumption
    case inr h =>
      have ⟨δ, h_δ, _⟩ := h
      exists δ
      apply Or.inl
      apply ℤ.sound
      show a + 0 = δ + b
      rw [ℕ.results.arithmetic.add_zero, ℕ.results.arithmetic.add_comm]
      assumption
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

    theorem neg_add' {x y : ℤ} : - (x + y) = -x + -y := by
      apply x.indOn ; intro (a, b)
      apply y.indOn ; intro (x, y)
      rw [add_mk, neg_mk, neg_mk, neg_mk, add_mk] -- closed by `rfl`

    theorem neg_zero : -(0 : ℤ) = 0 := by
      rw [← ntn_zero, neg_mk]
  end arith



  /- SECTION: Multiplication: Definition, assoc, comm, mul_one, one_mul, mul_zero, zero_mul -/
  def pair_mul : ℕ × ℕ → ℕ × ℕ → ℕ × ℕ
    | (a, b), (x, y) =>
      (a * x + b * y, a * y + b * x)

  open ℕ.results in
  /-- Multiplication on `ℤ`. Defined by lifting to the quotient. -/
  def mul (x : ℤ) (y : ℤ) : ℤ :=
    Quotient.liftOn₂ x y
      (fun p q => ℤ.mk $ pair_mul p q)
      $ by -- Proof that `ℤ.mk ∘ pair_mul` (put in necessary currying/uncurrying to make that typecheck) respects `same_difference`
        -- NOTE: This proof is miserable and I've done it terribly inefficiently.
        -- I learned:
        --    `ℕ.results.arithmetic.add_right_comm` is *super* useful, actually!
        --    I should learn to write my own tactics. At least in Lean3, this involves monadic code; I bet I could figure that out
        --    `ℕ.results.arithmetic.add_right_cancel` should be an `↔`, not a `→`; this would allow cancelling in a goal with just a simple `rw`
        --    `ℕ.results.arithmetic` is a huge pain in the ass to type out over and over.
        --      As nice as it is to keep things exported from `ℕ.results` and have them further subdivided from within
        --        there, I think `results.ℕ` (with an `open results` at the top of a file like this) with no further subdivision would be
        --        better.
        --      I'm in a bit too deep to go back and change *all* of that now though, including for `/Results/Integer.lean`.
        --      I'll design my namespace tree a bit better next time, and make more judicious use of `export`. A file like:
        --        ` /- @file Working/Stuff.lean -/          `
        --        ` namespace short.working                 `
        --        `   def thingIDontWannaSeeLater : ⋯ := ⋯  `
        --        `                                         `
        --        `   def thingIWannaSeeLater : ⋯ := ⋯      `
        --        `   export short (thingIWannaSeeLater)    ` -- notice the `export` here
        --        `   ⋯                                     `
        --        ` end short.working                       `
        --        might be better for my use case. Would have to try it out to really see...
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
        conv => {
          lhs
          repeat rw [arithmetic.add_right_comm (b * y')]
          rw [arithmetic.add_comm _ (b * y')]
        }
        rw [arithmetic.add_right_comm (b * x)]
        rw [arithmetic.add_comm _ (b * x)]
        rw [← arithmetic.mul_add, h_xy, arithmetic.mul_add]
        conv => {
          rhs
          repeat rw [arithmetic.add_right_comm (b' * x)]
          rw [arithmetic.add_comm _ (b' * x)]
        }
        rw [← @arithmetic.mul_add b', h_xy, @arithmetic.mul_add b']
        conv => {
          rhs
          repeat rw [arithmetic.add_right_comm (a * x')]
          rw [arithmetic.add_comm _ (a * x')]
        }
        rw [← @arithmetic.add_mul _ _ x', h_ab, @arithmetic.add_mul _ _ x']
        rw [arithmetic.add_comm (a' * x')]
        repeat rw [← arithmetic.add_assoc]
        rw [← @arithmetic.mul_add b, h_xy, @arithmetic.mul_add b]
        repeat rw [arithmetic.add_assoc]
        conv => {
          rhs
          repeat rw [arithmetic.add_right_comm (b * y)]
        }
        repeat rw [arithmetic.add_right_comm (b * x')]
        conv => {
          rhs
          repeat rw [← arithmetic.add_assoc]
          rw  [ ← @arithmetic.add_mul _ _ y
              ,   arithmetic.add_comm b' a
              ,   h_ab
              ,   @arithmetic.add_mul _ _ y
              ]
          repeat rw [arithmetic.add_assoc]
        }
        repeat rw [arithmetic.add_right_comm (a' * y)]
        conv => {
          rhs
          rw [← arithmetic.add_right_comm (a' * x')]
        }
        -- Finally closed by `rfl`
  instance instMul : Mul ℤ where mul := ℤ.mul
  namespace arith
    /-- The defining property of `ℤ.mul`: it does that stuff on arguments of the form `ℤ.mk (thing : ℕ × ℕ)`. -/
    theorem mul_mk {a b x y : ℕ} : (ℤ.mk (a, b)) * (ℤ.mk (x, y)) = ℤ.mk (a * x + b * y, a * y + b * x) := rfl

    -- NOTE: assoc
    open ℕ.results in
    /-- Associativity of `ℤ.mul`. -/
    theorem mul_assoc {x y z : ℤ} : x * (y * z) = (x * y) * z := by
      -- Boilerplate
      apply ℤ.indOn x ; intro (a, b)
      apply ℤ.indOn y ; intro (p, q)
      apply ℤ.indOn z ; intro (x, y)
      repeat rw [mul_mk]
      apply ℤ.sound
      -- Do stuff
      show (a * (p * x + q * y) + b * (p * y + q * x)) + ((a * p + b * q) * y + (a * q + b * p) * x) = ((a * p + b * q) * x + (a * q + b * p) * y) + (a * (p * y + q * x) + b * (p * x + q * y))
      -- NOTE: This is exactly what `simp` was designed for...
      repeat rw [arithmetic.mul_add]
      repeat rw [arithmetic.add_mul]
      repeat rw [arithmetic.add_assoc]
      repeat rw [arithmetic.mul_assoc]
      -- NOTE: You're about to witness the perfect advertisement for "creating your own tactic".
      -- Shove `a * p * x` to the right-most position on both sides of `=` in the goal
      conv => {
        pattern (occs := *) (a * p * x + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * p * x)]
      -- Shove `a * q * y` away
      conv => {
        pattern (occs := *) (a * q * y + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * q * y)]
      -- Shove `b * p * y` away
      conv => {
        pattern (occs := *) (b * p * y + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * p * y)]
      -- Shove `b * q * x` away
      conv => {
        pattern (occs := *) (b * q * x + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * q * x)]
      -- Shove `a * p * y` away
      conv => {
        pattern (occs := *) (a * p * y + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * p * y)]
      -- Shove `b * q * y` away
      conv => {
        pattern (occs := *) (b * q * y + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * q * y)]
      -- Finally closed by `rfl`

    -- NOTE: comm
    open ℕ.results in
    /-- Commutativity of `ℤ.mul`. -/
    theorem mul_comm (x y : ℤ) : x * y = y * x := by
      apply ℤ.indOn x ; intro (a, b)
      apply ℤ.indOn y ; intro (x, y)
      repeat rw [mul_mk]
      apply ℤ.sound
      show (a * x + b * y) + (x * b + y * a) = (x * a + y * b) + (a * y + b * x)
      -- fake `simp`
      repeat rw [arithmetic.add_assoc]
      -- Shove `a * x` away
      rw [arithmetic.mul_comm x a]
      conv => {
        pattern (occs := *) (a * x + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * x)]
      -- Shove `b * y` away
      rw [arithmetic.mul_comm y b]
      conv => {
        pattern (occs := *) (b * y + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * y)]
      -- Shove `b * x` away
      rw [arithmetic.mul_comm x b]
      conv => {
        pattern (occs := *) (b * x + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * x)]
      -- Close out with `y * a = a * y`
      rw [arithmetic.mul_comm a y]

    open ℕ.results in
    theorem mul_one {x : ℤ} : x * 1 = x := by
      apply ℤ.indOn x ; intro (x, y)
      rw [← ntn_one]
      rw [mul_mk]
      apply ℤ.sound
      show (x * 1 + y * 0) + y = x + (x * 0 + y * 1)
      rw [arithmetic.mul_one, arithmetic.mul_zero, arithmetic.add_zero, arithmetic.mul_zero, arithmetic.zero_add, arithmetic.mul_one]
    theorem one_mul {x : ℤ} : 1 * x = x := by
      rw [mul_comm] ; exact mul_one

    open ℕ.results in
    theorem mul_zero {x : ℤ} : x * 0 = 0 := by
      apply ℤ.indOn x ; intro (x, y)
      rw [← ntn_zero, mul_mk]
      apply ℤ.sound
      show (x * 0 + y * 0) + 0 = 0 + (x * 0 + y * 0)
      rw [arithmetic.mul_zero, arithmetic.zero_add, arithmetic.mul_zero]
    theorem zero_mul {x : ℤ} : 0 * x = 0 := by
      rw [mul_comm] ; exact mul_zero
  end arith



  /- SECTION: Multiplication by negatives -/
  namespace arith
    open ℕ.results in
    theorem mul_neg_1 {x : ℤ} : x * (-1) = -x := by
      apply x.indOn ; intro (x, y)
      rw [← ntn_one, neg_mk, neg_mk, mul_mk]
      apply ℤ.sound
      show (x * 0 + y * 1) + x = y + (x * 1 + y * 0)
      rw  [ arithmetic.mul_zero
          , arithmetic.zero_add
          , arithmetic.mul_one
          , arithmetic.mul_one
          , arithmetic.mul_zero
          , arithmetic.add_zero]

    theorem neg_1_mul {x : ℤ} : (-1) * x = -x := by
      rw [mul_comm] ; exact mul_neg_1
  end arith



  /- SECTION: Subtraction -/
  def sub (x y : ℤ) : ℤ := x + (-y)
  instance : Sub ℤ where sub := ℤ.sub
  namespace arith
    -- TODO: Actually prove the results about subtraction here
    theorem sub_eq_add_neg {x y : ℤ} : x - y = x + -y := rfl

    theorem sub_self {x : ℤ} : x - x = 0 := by
      rw [sub_eq_add_neg]
      exact add_neg

    theorem sub_neg {x y : ℤ} : x - -y = x + y := by
      rw [sub_eq_add_neg, neg_neg]

    theorem neg_sub {x y : ℤ} : - (x + y) = -x - y := by
      apply Eq.symm
      rw [sub_eq_add_neg, neg_add']

    theorem zero_sub {x : ℤ} : 0 - x = -x := by
      rw [sub_eq_add_neg, zero_add]
    theorem sub_zero {x : ℤ} : x - 0 = x := by
      rw [sub_eq_add_neg, neg_zero, add_zero]
  end arith



  /- SECTION: Distributivity -/
  namespace arith
    open ℕ.results in
    theorem mul_add {a x y : ℤ} : a * (x + y) = a * x + a * y := by
      apply a.indOn ; intro (a, b)
      apply x.indOn ; intro (p, q)
      apply y.indOn ; intro (x, y)
      rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk]
      apply ℤ.sound
      show (a * (p + x) + b * (q + y)) + (a * q + b * p + (a * y + b * x)) =
            (a * p + b * q + (a * x + b * y) + (a * (q + y) + b * (p + x)))
      repeat rw [arithmetic.mul_add]
      repeat rw [arithmetic.add_assoc]
      -- Shove `a * p` away
      conv => {
        pattern (occs := *) (a * p + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * p)]
      -- Shove `a * x` away
      conv => {
        pattern (occs := *) (a * x + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * x)]
      -- Shove `b * q` away
      conv => {
        pattern (occs := *) (b * q + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * q)]
      -- Shove `b * y` away
      conv => {
        pattern (occs := *) (b * y + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * y)]
      -- Shove `a * q` away
      conv => {
        pattern (occs := *) (a * q + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (a * q)]
      -- Shove `b * p` away
      conv => {
        pattern (occs := *) (b * p + _)
        <;> rw [arithmetic.add_comm]
      }
      repeat rw [← arithmetic.add_right_comm (b * p)]
      -- Finally closed by `rfl`

    theorem add_mul {a b x : ℤ} : (a + b) * x = a * x + b * x := by
      rw [mul_comm _ x, mul_comm a _, mul_comm b _]
      exact mul_add ..
  end arith



  /- SECTION: Right commutativity my beloved, `swap_sub`, `eq_of_sub_eq_zero` -/
  namespace arith
    theorem add_right_comm {x y : ℤ} (z : ℤ) : x + y + z = x + z + y := by
      repeat rw [← add_assoc]
      rw [add_comm y]

    theorem swap_sub {x y : ℤ} : - (x - y) = y - x := by
      rw [sub_eq_add_neg, sub_eq_add_neg, neg_add', neg_neg, add_comm]

    theorem eq_of_sub_eq_zero {x y : ℤ} : x - y = 0 → x = y := by
      intro h
      calc x
        _ = x + 0         := add_zero.symm
        _ = x + (y - y)   := by rw [←sub_self]
        _ = x + (y + -y)  := by rw [sub_eq_add_neg]
        _ = x + (-y + y)  := by rw [add_comm y]
        _ = x + -y + y    := by rw [add_assoc]
        _ = x - y + y     := by rw [←sub_eq_add_neg]
        _ = 0 + y         := by rw [h]
        _ = y             := zero_add
    theorem eq_iff_sub_eq_zero {x y : ℤ} : x - y = 0 ↔ x = y := by
      constructor
      case mp  => exact eq_of_sub_eq_zero
      case mpr => intro h ; rw [h, sub_self]

    theorem add_sub_assoc {x y z : ℤ} : x + (y - z) = x + y - z := calc x + (y - z)
      _ = x + (y + -z)  := by rw [sub_eq_add_neg]
      _ = (x + y) + -z  := by rw [add_assoc]
      _ = x + y - z     := by rw [sub_eq_add_neg]

    theorem sub_add {x y z : ℤ} : x - (y + z) = x - y - z := by
      rw [sub_eq_add_neg, neg_add', add_assoc, sub_eq_add_neg, sub_eq_add_neg]

    theorem neg_eq_comm {x y : ℤ} : -x = y ↔ -y = x := by
      have lemma : ∀ (a b : ℤ), -a = b → -b = a := by
        intro a b
        apply a.indOn ; intro (p, q)
        apply b.indOn ; intro (x, y)
        rw [neg_mk, neg_mk]
        intro h
        have h : q + y = x + p := ℤ.exact h
        apply ℤ.sound
        show y + q = p + x
        rw [ℕ.results.arithmetic.add_comm y, ℕ.results.arithmetic.add_comm p]
        exact h
      constructor <;> apply lemma
  end arith



  /- SECTION: `≤`: Definition, partial order, compatability -/
  def le (x y : ℤ) : Prop :=
    ∃ (a : ℕ), y - x = ℤ.mk (a, 0)
  instance : LE ℤ where le := ℤ.le
  namespace order
    open arith

    theorem le_ntn {x y : ℤ} : x.le y = (x ≤ y) := rfl

    /-- Defining property of `ℤ.le`. -/
    theorem le_mk {x y : ℤ} : x ≤ y ↔ ∃ (a : ℕ), y - x = ℤ.mk (a, 0) := by
      show x.le y ↔ ∃ a, y - x = ℤ.mk (a, 0)
      rfl

    theorem le_refl (x : ℤ) : x ≤ x := by
      exists 0
      rw [ntn_zero]
      exact arith.sub_self
    theorem le_antisymm {x y : ℤ} : x ≤ y → y ≤ x → x = y := by
      intro ⟨a, h_a⟩ ⟨b, h_b⟩
      rw [←swap_sub, h_a, neg_mk] at h_b
      have h : 0 + 0 = b + a := ℤ.exact h_b
      rw [ℕ.results.arithmetic.zero_add] at h
      have h := ℕ.results.arithmetic.args_0_of_add_0 h.symm |> And.right
      rw [h, ntn_zero] at h_a
      exact eq_of_sub_eq_zero h_a |> .symm
    theorem le_trans {x y z : ℤ} : x ≤ y → y ≤ z → x ≤ z := by
      intro ⟨a, h_a⟩ ⟨b, h_b⟩
      have : z - x = ℤ.mk (b + a, 0) := calc z - x
        _ = z - x + 0                 := by rw [add_zero]
        _ = z - x + (y - y)           := by rw [sub_self]
        _ = z - x + (y + -y)          := by rw [@sub_eq_add_neg y]
        _ = z + -x + (y + -y)         := by rw [@sub_eq_add_neg z]
        _ = z + -x + y + -y           := by repeat rw [add_assoc]
        _ = z + -y + -x + y           := by repeat rw [add_right_comm (-y)]
        _ = z + -y + y + -x           := by rw [add_right_comm y]
        _ = z - y + y + -x            := by rw [sub_eq_add_neg]
        _ = z - y + y - x             := by rw [←sub_eq_add_neg]
        _ = z - y + (y - x)           := by rw [←add_sub_assoc]
        _ = ℤ.mk (b, 0) + ℤ.mk (a, 0) := by rw [h_b, h_a]
        _ = ℤ.mk (b + a, 0)           := add_mk
      exists b + a

    theorem le_add_hom {a b x y : ℤ} : a ≤ b → x ≤ y → a + x ≤ b + y := by
      intro ⟨p, h_p⟩ ⟨q, h_q⟩
      show ∃ (r : ℕ), (b + y) - (a + x) = ℤ.mk (r, 0)
      conv => {
        arg 1 ; intro r ;
        rw  [   sub_add
            ,   sub_eq_add_neg
            ,   sub_eq_add_neg
            ,   add_right_comm (-a)
            , ← @sub_eq_add_neg b
            , ←add_assoc
            , ← @sub_eq_add_neg y
            ,   h_p
            ,   h_q
            ,   add_mk
            ,   ℕ.results.arithmetic.add_zero]
      }
      exists p + q

    theorem le_neg_antihom {x y : ℤ} : x ≤ y → -y ≤ -x := by
      intro ⟨a, h_a⟩
      show ∃ b, -x - -y = mk (b, 0)
      conv => {
        arg 1 ; intro b ;
        rw [sub_eq_add_neg, neg_neg, add_comm, ←sub_eq_add_neg]
      }
      exists a

    theorem le_of_nat {x : ℕ} : (0 : ℤ) ≤ (x : ℤ) := by
      exists x
  end order



  /- SECTION: `<`: Definition, etc. -/
  def lt (x y : ℤ) : Prop := x ≤ y ∧ x ≠ y
  instance : LT ℤ where lt := ℤ.lt
  namespace order
    open arith

    theorem lt_ntn {x y : ℤ} : x.lt y = (x < y) := rfl

    theorem lt_iff_le_and_ne {x y : ℤ} : x < y ↔ x ≤ y ∧ x ≠ y := by
      rw [←lt_ntn, ℤ.lt]

    theorem le_or_eq_iff_le {x y : ℤ} : x ≤ y ∨ x = y ↔ x ≤ y := by
      constructor
      case mp =>
        intro h ; cases h
        case inl h => assumption
        case inr h => rw [h] ; exact le_refl y
      case mpr => exact Or.inl

    -- NOTE: Uses classical logic
    theorem le_iff_lt_or_eq {x y : ℤ} : x ≤ y ↔ x < y ∨ x = y := by
      rw [lt_iff_le_and_ne]
      conv => {
        rhs
        rw [and_or_right]
        congr
        case a => {
          rw [le_or_eq_iff_le]
        }
      }
      constructor
      case mpr => exact And.left
      case mp =>
        intro h
        constructor
        · assumption
        · exact Classical.em _ |> Or.symm

    theorem lt_irrefl (x : ℤ) : ¬ (x < x) := by
      intro h
      rw [lt_iff_le_and_ne] at h
      have h := h.right
      contradiction -- `x ≠ x`

    -- NOTE: Uses classical logic
    theorem lt_asymm {x y : ℤ} : x < y → ¬ (y < x) := by
      repeat rw [lt_iff_le_and_ne]
      intro ⟨h_x_le_y, _⟩
      rw [not_and]
      intro h_y_le_x
      have := le_antisymm h_x_le_y h_y_le_x
      rw [Classical.not_not, Eq.comm]
      assumption

    theorem lt_trans {x y z : ℤ} : x < y → y < z → x < z := by
      intro h_xy h_yz
      rw [lt_iff_le_and_ne]
      constructor
      case left =>
        rw [lt_iff_le_and_ne] at h_xy ; have h_xy := h_xy.left
        rw [lt_iff_le_and_ne] at h_yz ; have h_yz := h_yz.left
        exact le_trans h_xy h_yz
      case right =>
        intro h
        rw [h] at h_xy
        exact lt_asymm h_xy h_yz

    /-- Not actually the defining relationship. -/
    theorem lt_mk {x y : ℤ} : x < y ↔ ∃ (a : ℕ), y - x = ℤ.mk (a, 0) ∧ a ≠ 0 := by
      rw [lt_iff_le_and_ne]
      constructor
      case mp =>
        intro ⟨⟨a, h_a⟩, h_x_ne_y⟩
        exists a
        constructor
        case left => assumption
        case right =>
          intro h_a_eq_0
          rw [h_a_eq_0, ntn_zero] at h_a
          have := eq_of_sub_eq_zero h_a |> Eq.symm
          contradiction -- `x ≠ y` and `x = y`
      case mpr =>
        intro ⟨a, h_a, h_a_ne_0⟩
        constructor
        case right =>
          intro h_x_eq_y
          show False
          rw [h_x_eq_y, sub_self, ← ntn_zero] at h_a
          have silver_bullet : 0 + 0 = a + 0 := ℤ.exact h_a
          rw [ℕ.results.arithmetic.add_zero, ℕ.results.arithmetic.add_zero, Eq.comm] at silver_bullet
          contradiction -- `a ≠ 0` and `a = 0`
        case left =>
          show ∃ b, y - x = ℤ.mk (b, 0)
          exists a

    theorem sub_le {x y z : ℤ} : x - y ≤ z ↔ x ≤ z + y := by
      show (∃ a, z - (x - y) = mk (a, 0)) ↔ (∃ a, z + y - x = mk (a, 0))
      conv => {
        lhs; arg 1; intro a
        rw  [ sub_eq_add_neg
            , sub_eq_add_neg
            , neg_add'
            , neg_neg
            , add_comm (-x)
            , add_assoc
            , ← sub_eq_add_neg]
      }
      -- closed by `rfl`
    theorem le_sub {x y z : ℤ} : x ≤ y - z ↔ x + z ≤ y := by
      show (∃ a, y - z - x = mk (a, 0)) ↔ (∃ a, y - (x + z) = mk (a, 0))
      conv => {
        rhs; arg 1; intro a; lhs
        rw [sub_eq_add_neg, neg_add', add_comm (-x), add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]
      }
      -- closed by `rfl`
    theorem sub_lt {x y z : ℤ} : x - y < z ↔ x < z + y := by
      rw [lt_mk, lt_mk]
      show (∃ a, z - (x - y) = mk (a, 0) ∧ a ≠ 0) ↔ (∃ a, z + y - x = mk (a, 0) ∧ a ≠ 0)
      -- Same proof as `sub_le` from here onwards
      conv => {
        lhs; arg 1; intro a
        rw  [ sub_eq_add_neg
            , sub_eq_add_neg
            , neg_add'
            , neg_neg
            , add_comm (-x)
            , add_assoc
            , ← sub_eq_add_neg]
      }
    theorem lt_sub {x y z : ℤ} : x < y - z ↔ x + z < y := by
      rw [lt_mk, lt_mk]
      show (∃ a, y - z - x = mk (a, 0) ∧ a ≠ 0) ↔ (∃ a, y - (x + z) = mk (a, 0) ∧ a ≠ 0)
      -- same proof as `le_sub` now
      conv => {
        rhs; arg 1; intro a; lhs
        rw [sub_eq_add_neg, neg_add', add_comm (-x), add_assoc, ←sub_eq_add_neg, ←sub_eq_add_neg]
      }
      -- closed by `rfl`

    theorem lt_iff_not_ge {x y : ℤ} : x < y ↔ ¬ (x ≥ y) := by
      constructor
      case mp =>
        rw [lt_mk]
        intro ⟨a, h_a, h_a_ne_0⟩
        intro ⟨b, h_b⟩
        rw [sub_eq_add_neg, add_comm, ←@neg_neg x, ←neg_add', ←sub_eq_add_neg] at h_b
        rw [h_a, neg_mk] at h_b
        have : 0 + 0 = b + a := ℤ.exact h_b
        rw [ℕ.results.arithmetic.add_zero, Eq.comm] at this
        have := ℕ.results.arithmetic.args_0_of_add_0 this |> And.right
        contradiction -- `a ≠ 0` and `a = 0`
      case mpr =>
        apply x.indOn ; intro (a, b)
        apply y.indOn ; intro (x, y)
        intro h
        rw [lt_mk]
        conv at h => {
          arg 1; rw [ge_iff_le, le_mk]
        }
        conv => {
          arg 1 ; intro n
          rw [sub_eq_add_neg, add_comm, ←@neg_neg (mk (x, y)), ←neg_add', ←sub_eq_add_neg]
          rw [neg_eq_comm, neg_mk, Eq.comm]
        }
        have h : ∀ n, mk (a, b) - mk (x, y) ≠ mk (n, 0) := by
          rw [not_exists] at h
          exact h
        have ⟨n, h_n⟩ := (mk (a, b) - mk (x, y)).existsCanonRep
        cases h_n
        case inl h_n =>
          suffices False by contradiction
          show False
          exact h n h_n
        case inr h_n =>
          exists n
          rw [h_n]
          constructor
          · rfl
          · intro h_n_eq_0
            show False
            rw [h_n_eq_0] at h_n
            exact h 0 h_n

    -- Uses `Classical` logic
    theorem lt_trichotomy (x y : ℤ) : x < y ∨ x = y ∨ y < x := by
      have lemma : ∀ (x : ℤ), 0 < x ∨ 0 = x ∨ x < 0 := by
        intro x ; apply x.indOn ; intro (x, y)
        by_cases h : 0 ≤ mk (x, y)
        case pos => -- `h : 0 ≤ mk (x, y)`
          rw [le_mk] at h
          have ⟨a, h_a⟩ := h
          rw [sub_zero] at h_a
          match a with
          | 0 =>
            rw [ntn_zero] at h_a
            exact h_a.symm |> Or.inl |> Or.inr
          | .succ a =>
            apply Or.inl
            rw [←ntn_zero, lt_mk, ntn_zero, sub_zero]
            show ∃ a, mk (x, y) = mk (a, 0) ∧ a ≠ 0
            exists a.succ
            constructor
            case h.right =>
              intro h ; injection h
            case h.left =>
              apply ℤ.sound
              show x + 0 = a.succ + y
              exact ℤ.exact h_a
        case neg => -- `h : ¬ (0 ≤ mk (x, y))`
          apply Or.inr ; apply Or.inr
          show mk (x, y) < 0
          rw [lt_iff_not_ge]
          exact h
      -- Straightforward application of the `lemma`
      have := lemma <| y - x
      rw [lt_sub, zero_add] at this
      rw [Eq.comm, eq_iff_sub_eq_zero, Eq.comm] at this
      rw [sub_lt, zero_add] at this
      assumption
  end order



  /- SECTION: Divisibility -/
  /-- The divisibility relation on `ℤ`. -/
  def divides (d x : ℤ) : Prop := ∃ (q : ℤ), x = d * q
  @[inherit_doc] infix:50 " ∣ " => divides

  namespace divisibility
    open arith

    theorem divides_refl (x : ℤ) : x ∣ x := by
      exists 1
      rw [mul_one]
    theorem divides_symm {x y : ℤ} : x ∣ y → y ∣ x → x = y ∨ x = -y := by
      intro ⟨q, h_q⟩ ⟨r, h_r⟩
      rw [h_q] at h_r
      admit
  end divisibility

  -- def prime (p : ℤ) : Prop := p > 1 ∧ ∀ (d : ℤ)
end ℤ

end Numbers
