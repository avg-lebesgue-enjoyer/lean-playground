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
  -- TODO: More results
end ℤMod

end Numbers
