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


end Numbers
