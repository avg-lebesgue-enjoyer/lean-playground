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
  @[simp] theorem ntn_zero_eq_0 : ℕ.zero = 0 := rfl
  @[simp] theorem ntn_succ_zero_eq_1 : ℕ.succ ℕ.zero = 1 := rfl

  /- SECTION: Addition -/
  def add (x : ℕ) : ℕ → ℕ
    | 0       => x
    | .succ y => .succ $ x.add y
  instance : Add ℕ where add := ℕ.add
  namespace add
    @[simp] theorem ntn_add_eq_add : ∀ {x y : ℕ}, x.add y = x + y := rfl
    @[simp] theorem lem_add_0
      (x : ℕ)
      : x + 0 = x
      := rfl
    @[simp] theorem lem_add_succ
      (x y : ℕ)
      : x + succ y = succ (x + y)
      := rfl

    @[simp] theorem lem_0_add
      (x : ℕ)
      : 0 + x = x
      := match x with
      | 0 => rfl
      | succ x => by rw [lem_add_succ, lem_0_add]
    @[simp] theorem lem_succ_add
      (x y : ℕ)
      : succ x + y = succ (x + y)
      := match y with
      | 0 => rfl
      | succ y => by rw [lem_add_succ x.succ y, lem_add_succ x y, lem_succ_add x y]

    @[simp] theorem thm_assoc
      (x y z : ℕ)
      : (x + y) + z = x + (y + z)
      := match z with
      | 0 => rfl
      | succ z => by rw [lem_add_succ, lem_add_succ, lem_add_succ, thm_assoc x y z]
    @[simp] theorem thm_comm
      (x y : ℕ)
      : x + y = y + x
      := match y with
      | 0 => by rw [lem_add_0, lem_0_add]
      | succ y => by rw [lem_add_succ, lem_succ_add, thm_comm x y]

    theorem thm_args_0_of_add_0
      (x y : ℕ)
      : x + y = 0
      → x = 0 ∧ y = 0
      := fun h => match x, y with
      | 0, 0 => And.intro rfl rfl
      | _, succ y => by contradiction
      | succ x, _ => by rw [lem_succ_add] at h ; contradiction
    @[simp] theorem thm_right_cancel
      (c x y : ℕ)
      : x + c = y + c
      → x = y
      := fun h => match c with
      | 0 => h
      | succ c => by rw [lem_add_succ, lem_add_succ] at h ; injection h with h ; exact thm_right_cancel c x y h
    @[simp] theorem thm_left_cancel
      (c x y : ℕ)
      : c + x = c + y
      → x = y
      := by rw [thm_comm c x, thm_comm c y] ; exact thm_right_cancel c x y
  end add
end ℕ

end Numbers



/- LAUNCH: List of results -/
namespace Numbers.ℕ
  -- SECTION: Notation
  #check ntn_zero_eq_0
  #check ntn_succ_zero_eq_1
  #check add.ntn_add_eq_add



  -- SECTION: Induction and Well-Ordering
  #check ℕ.rec



  -- SECTION: Addition
  namespace add
    #check lem_add_0
    #check lem_add_succ
    #check lem_0_add
    #check lem_succ_add

    #check thm_assoc
    #check thm_comm

    #check thm_args_0_of_add_0
    #check thm_right_cancel
    #check thm_left_cancel
  end add

  /- SECTION: Results yet to be proven
    [2.] Multiplication:

    [3.] Order (<, >, ≤ and ≥):
      (include well-foundedness of `<`)
      (include well-ordering principle ("strong induction"))

    [4.] Induction from bases other than 0
      (include "strong" variants)
  -/
end Numbers.ℕ
