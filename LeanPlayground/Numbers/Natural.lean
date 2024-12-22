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

  /- SECTION: Successor -/
  namespace succ
    @[simp] theorem zero_not_succ (x : ℕ) : x.succ ≠ 0 := by
      intro h ; injection h
  end succ



  /- SECTION: Addition -/
  def add (x : ℕ) : ℕ → ℕ
    | 0       => x
    | .succ y => .succ $ x.add y
  instance : Add ℕ where add := ℕ.add
  namespace add
    @[simp] theorem ntn : ∀ {x y : ℕ}, x.add y = x + y := rfl
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
      : x + (y + z) = (x + y) + z
      := match z with
      | 0 => rfl
      | succ z => by rw [lem_add_succ, lem_add_succ, lem_add_succ, thm_assoc x y z]
    theorem thm_comm
      (x y : ℕ)
      : x + y = y + x
      := match y with
      | 0 => by rw [lem_add_0, lem_0_add]
      | succ y => by rw [lem_add_succ, lem_succ_add, thm_comm x y]

    theorem thm_args_0_of_add_0
      {x y : ℕ}
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

    @[simp] theorem arg_1_of_add_1
      (x y : ℕ)
      : x + y = 1
      → x = 1 ∨ y = 1
      := fun h => match x, y with
      | 0, 0 => by contradiction
      | x, succ y => by
        rw [add.lem_add_succ, ←ntn_succ_zero_eq_1] at h ; injection h with h ; rw [ntn_zero_eq_0] at h
        have h : y = 0 := (add.thm_args_0_of_add_0 h).right
        apply Or.inr
        rw [h]
        rfl
      | succ x, y => by
        rw [add.lem_succ_add, ←ntn_succ_zero_eq_1] at h ; injection h with h ; rw [ntn_zero_eq_0] at h
        have h : x = 0 := (add.thm_args_0_of_add_0 h).left
        apply Or.inl
        rw [h]
        rfl
  end add


  /- SECTION: Multiplication -/
  def mul (x : ℕ) : ℕ → ℕ
    | 0 => 0
    | succ y => x.mul y + x
  instance : Mul ℕ where mul := ℕ.mul
  namespace mul
    @[simp] theorem ntn : ∀ {x y : ℕ}, x.mul y = x * y := rfl
    @[simp] theorem lem_mul_0
      (x : ℕ)
      : x * 0 = 0
      := rfl
    @[simp] theorem lem_mul_succ
      (x y : ℕ)
      : x * succ y = x * y + x
      := rfl

    @[simp] theorem lem_0_mul
      (x : ℕ)
      : 0 * x = 0
      := match x with
      | 0 => rfl
      | succ x => by rw [lem_mul_succ, lem_0_mul x, add.lem_add_0]
    @[simp] theorem lem_succ_mul
      (x y : ℕ)
      : succ x * y = x * y + y
      := match y with
      | 0 => rfl
      | succ y => calc succ x * succ y
        _ = x.succ * y + x.succ     := rfl
        _ = x * y  + y + x.succ     := congrArg (· + x.succ) $ lem_succ_mul x y
        _ = (x * y + y + x).succ    := rfl
        _ = (x * y + (y + x)).succ  := congrArg succ $ (add.thm_assoc ..).symm
        _ = (x * y + (x + y)).succ  := congrArg (succ $ x * y + ·) $ add.thm_comm y x
        _ = (x * y + x + y).succ    := congrArg succ $ add.thm_assoc ..
        _ = x * y  + x + y.succ     := rfl
        _ = x * succ y + succ y     := rfl

    @[simp] theorem thm_add_mul
      (a b x : ℕ)
      : (a + b) * x = a * x + b * x
      := match x with
      | 0 => rfl
      | succ x => by
        simp [lem_mul_succ, thm_add_mul a b x]
        calc a * x + b * x + a + b
          _ = a * x + b * x + (a + b)   := by rw [←add.thm_assoc]
          _ = a * x + (b * x + (a + b)) := by rw [←add.thm_assoc]
          _ = a * x + ((b * x + a) + b) := by rw [add.thm_assoc (b * x)]
          _ = a * x + ((a + b * x) + b) := by rw [add.thm_comm _ a]
          _ = a * x + a + b * x + b     := by simp

    theorem thm_comm
      (x y : ℕ)
      : x * y = y * x
      := match y with
      | 0 => by rw [lem_0_mul, lem_mul_0]
      | succ y => by rw [lem_mul_succ, lem_succ_mul, thm_comm x y]

    @[simp] theorem thm_mul_add
      (a x y : ℕ)
      : a * (x + y) = a * x + a * y
      := by
        rw [thm_comm a _, thm_comm a _, thm_comm a _]
        apply thm_add_mul

    @[simp] theorem thm_assoc
      (x y z : ℕ)
      : x * (y * z) = (x * y) * z
      := match z with
      | 0 => rfl
      | succ z => by
        rw [lem_mul_succ, lem_mul_succ]
        rw [thm_mul_add]
        rw [thm_assoc x y z]

    @[simp] theorem lem_mul_1
      (x : ℕ)
      : x * 1 = x
      := by
        rw [←ntn_succ_zero_eq_1, lem_mul_succ, ntn_zero_eq_0, lem_mul_0, add.lem_0_add]
    @[simp] theorem lem_1_mul
      (x : ℕ)
      : 1 * x = x
      := by
        rw [thm_comm 1]
        apply lem_mul_1

    -- This proof is disgusting. I'm sure I can make it better later...
    @[simp] theorem thm_args_1_of_mul_1
      (x y : ℕ)
      : x * y = 1
      → x = 1 ∧ y = 1
      := fun h =>
      match y with
      | 0 => by contradiction
      | succ y => by
        rw [lem_mul_succ] at h
        have h' : x = 1 :=
          match add.arg_1_of_add_1 _ _ h with
          | .inr h' => h'
          | .inl h' => (thm_args_1_of_mul_1 x y h').left
        have h'' : 1 = 0 + 1 := rfl
        rw [h', lem_1_mul] at h
        have h : y + 1 = 0 + 1 :=
          calc y + 1
            _ = 1 := h
            _ = 0 + 1 := rfl
        have h : y = 0 := by apply add.thm_right_cancel 1 ; assumption
        rw [h]
        constructor ; assumption ; rfl

    /-- aka. null factor law -/
    @[simp] theorem thm_arg_0_of_mul_0
      {x y : ℕ}
      (h : x * y = 0)
      : x = 0 ∨ y = 0
      := match y with
      | 0 => .inr rfl
      | succ y => .inl $ by
        rw [lem_mul_succ] at h
        exact (add.thm_args_0_of_add_0 h).right
    theorem thm_null_factor
      {x y : ℕ}
      : x * y = 0
      → x = 0 ∨ y = 0
      := thm_arg_0_of_mul_0

    -- This is a bit disgusting too
    @[simp] theorem thm_left_cancel
      (c x y : ℕ)
      (h_c_neq_0 : c ≠ 0)
      (h_eq : c * x = c * y)
      : x = y
      := match y with
      | 0 =>
        have h_eq : c * x = 0 := h_eq
        match (thm_null_factor h_eq) with
        | .inl h_c_eq_0 => absurd h_c_eq_0 h_c_neq_0
        | .inr h_x_eq_0 => h_x_eq_0
      | succ y => by
        rw [lem_mul_succ] at h_eq
        match x with
        | 0 =>
          rw [lem_mul_0] at h_eq
          have h_c_eq_0 := (add.thm_args_0_of_add_0 h_eq.symm).right
          exact absurd h_c_eq_0 h_c_neq_0
        | succ x =>
          rw [lem_mul_succ] at h_eq
          have h_eq := add.thm_right_cancel c _ _ h_eq
          have h_eq := thm_left_cancel c x y h_c_neq_0 h_eq
          rw [h_eq]
    @[simp] theorem thm_right_cancel
      (c x y : ℕ)
      (h_c_neq_0 : c ≠ 0)
      (h_eq : x * c = y * c)
      : x = y
      := by
        rw [thm_comm x c, thm_comm y c] at h_eq
        apply thm_left_cancel <;> assumption
  end mul
end ℕ

end Numbers



/- LAUNCH: List of results -/
namespace Numbers.ℕ
  -- SECTION: Notation
  #check ntn_zero_eq_0
  #check ntn_succ_zero_eq_1
  #check add.ntn
  #check mul.ntn



  -- SECTION: Induction and Well-Ordering
  #check ℕ.rec



  -- SECTION: Successor
  namespace succ
    #check inj
    #check zero_not_succ
  end succ



  -- SECTION: Addition
  namespace add
    #check lem_add_0
    #check lem_add_succ
    #check lem_0_add
    #check lem_succ_add

    #check thm_assoc
    #check thm_comm

    #check thm_args_0_of_add_0
    #check arg_1_of_add_1
    #check thm_right_cancel
    #check thm_left_cancel
  end add



  -- SECTION: Multiplication
  namespace mul
    #check lem_mul_0
    #check lem_mul_succ
    #check lem_0_mul
    #check lem_succ_mul
    #check lem_mul_1
    #check lem_1_mul

    #check thm_assoc
    #check thm_comm

    #check thm_mul_add
    #check thm_add_mul

    #check thm_args_1_of_mul_1
    #check thm_null_factor
    #check thm_left_cancel
    #check thm_right_cancel
  end mul

  /- SECTION: Results yet to be proven
    [3.] Order (<, >, ≤ and ≥):
      (include well-foundedness of `<`)
      (include well-ordering principle ("strong induction"))

    [4.] Induction from bases other than 0
      (include "strong" variants)

    [5.] Fundamental Theorem of Arithmetic
      (it)
  -/
end Numbers.ℕ
