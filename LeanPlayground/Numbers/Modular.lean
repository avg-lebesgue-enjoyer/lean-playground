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
