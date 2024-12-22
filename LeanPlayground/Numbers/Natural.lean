/- @file LeanPlayground/Numbers/Natural.lean
 - Theory of the natural numbers, probably
 -/
namespace Numbers
  /- SECTION: Defining ℕ -/
  inductive ℕ : Type where
    | zero : ℕ
    | succ : ℕ → ℕ
  instance : OfNat ℕ 0 where ofNat := .zero
  instance : OfNat ℕ 1 where ofNat := .succ .zero
  namespace ℕ
    @[simp] theorem lem_zero_eq_0 : ℕ.zero = 0 := rfl
    @[simp] theorem lem_succ_zero_eq_1 : ℕ.succ ℕ.zero = 1 := rfl

  end ℕ
end Numbers



/- LAUNCH: List of results -/
namespace Numbers.ℕ
  #check lem_zero_eq_0
end Numbers.ℕ
