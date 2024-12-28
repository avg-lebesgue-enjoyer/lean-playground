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
    @[simp] theorem lem_succ_eq_add_1
      (x : ℕ)
      : succ x = x + 1
      := by
        apply Eq.symm
        calc x + 1
          _ = x + succ 0    := rfl
          _ = succ (x + 0)  := rfl
          _ = succ x        := rfl

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
        calc (a + b) * x.succ
          _ = (a + b) * x + (a + b) := rfl
          _ = (a * x + b * x) + (a + b) := by rw [thm_add_mul a b x]
          _ = ((a * x + b * x) + a) + b := by rw [add.thm_assoc]
          _ = (a * x + (b * x + a)) + b := by rw [← add.thm_assoc (a * x)]
          _ = (a * x + (a + b * x)) + b := by rw [add.thm_comm _ a]
          _ = ((a * x + a) + b * x) + b := by rw [add.thm_assoc (a * x)]
          _ = (a * x.succ + b * x) + b  := rfl
          _ = a * x.succ + (b * x + b)  := by rw [← add.thm_assoc]
          _ = a * x.succ + b * x.succ   := rfl

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



  /- SECTION: Order -/
  def le (x : ℕ) (y : ℕ) : Prop := ∃ (δ : ℕ), y = x + δ
  instance : LE ℕ where le := ℕ.le
  namespace le
    @[simp] theorem ntn : ∀ {x y : ℕ}, x.le y = (x ≤ y) := rfl

    -- Verifying that `ℕ.le` is a partial order
    @[simp] theorem refl {x : ℕ} : x ≤ x := ⟨0, rfl⟩
    @[simp] theorem antisymm
      {x y : ℕ}
      (h_x_le_y : x ≤ y)
      (h_y_le_x : y ≤ x)
      : x = y :=
        let ⟨δ, h_δ⟩ := h_x_le_y
        let ⟨ε, h_ε⟩ := h_y_le_x
        have : x + 0 = x + (δ + ε) := calc x + 0
          _ = x           := rfl
          _ = y + ε       := h_ε
          _ = (x + δ) + ε := by rw [h_δ]
          _ = x + (δ + ε) := by rw [←add.thm_assoc]
        have : 0 = δ + ε := add.thm_left_cancel x 0 (δ + ε) this
        have : ε = 0 := (add.thm_args_0_of_add_0 this.symm).right
        show x = y from calc x
          _ = y + ε := h_ε
          _ = y + 0 := by rw [this]
          _ = y     := rfl
    @[simp] theorem trans
      {x y z : ℕ}
      (h_xy : x ≤ y)
      (h_yz : y ≤ z)
      : x ≤ z
      :=
        let ⟨δ, h_δ⟩ := h_xy
        let ⟨ε, h_ε⟩ := h_yz
        have : z = x + (δ + ε) := calc z
          _ = y + ε := by assumption
          _ = (x + δ) + ε := congrArg (· + ε) (by assumption)
          _ = x + (δ + ε) := by rw [←add.thm_assoc]
        show ∃ (φ : ℕ), z = x + φ from ⟨δ + ε, this⟩

    -- To use `≤` in `calc` blocks
    instance : Trans ℕ.le ℕ.le ℕ.le where trans := le.trans

    -- Lemmas to show respects addition
    theorem le_add_right
      {x δ : ℕ}
      : x ≤ x + δ
      := ⟨δ, rfl⟩
    theorem le_add_left
      {x δ : ℕ}
      : x ≤ δ + x
      := by
        rw [ℕ.add.thm_comm]
        exact le_add_right

    -- Respects addition
    theorem add_le_add
      {a b x y : ℕ}
      (h_ax : a ≤ x)
      (h_by : b ≤ y)
      : a + b ≤ x + y :=
        let ⟨δ, h_δ⟩ := h_ax
        let ⟨ε, h_ε⟩ := h_by
        show a + b ≤ x + y from calc a + b
          ℕ.le _ (a + b + δ) := le_add_right
          _ = a + δ + b := by rw [←add.thm_assoc, add.thm_comm b δ, add.thm_assoc]
          ℕ.le _ (a + δ + b + ε) := le_add_right
          _ = (a + δ) + (b + ε) := by rw [add.thm_assoc]
          _ = x + y := by rw [h_δ, h_ε]

    -- Respects multiplication
    theorem mul_le_mul
      {a b x y : ℕ}
      (h_ax : a ≤ x)
      (h_by : b ≤ y)
      : a * b ≤ x * y :=
        let ⟨δ, h_δ⟩ := h_ax
        let ⟨ε, h_ε⟩ := h_by
        have h : x * y = a * b + (δ * b + a * ε + δ * ε) := calc x * y
          _ = (a + δ) * (b + ε)                 := by rw [h_δ, h_ε]
          _ = (a + δ) * b + (a + δ) * ε         := by apply mul.thm_mul_add
          _ = (a * b + δ * b) + (a * ε + δ * ε) := by rw [mul.thm_add_mul, mul.thm_add_mul]
          _ = a * b + (δ * b + a * ε + δ * ε)   := by rw [←add.thm_assoc, add.thm_assoc (δ * b)]
        let φ := δ * b + a * ε + δ * ε
        show ∃ φ, x * y = a * b + φ from ⟨φ, h⟩

    -- `succ` is monotone increasing
    theorem succ_le_strong_hom
      {x y : ℕ}
      : x ≤ y ↔ x.succ ≤ y.succ
      := by
        have h_succ_as_add_1 : ∀ {a : ℕ}, a.succ = a + 1 := rfl
        constructor
        case mp =>
          intro
          rw [h_succ_as_add_1, h_succ_as_add_1]
          have : (1 : ℕ) ≤ 1 := le.refl
          apply add_le_add <;> assumption
        case mpr =>
          intro ⟨δ, h_δ⟩
          rw [h_succ_as_add_1, h_succ_as_add_1] at h_δ
          conv at h_δ => {
            rhs
            rw [←add.thm_assoc]
            rw [add.thm_comm 1 δ]
            rw [add.thm_assoc]
          }
          have h_δ : y = x + δ := add.thm_right_cancel 1 _ _ h_δ
          show ∃ δ, y = x + δ ; exact ⟨δ, h_δ⟩

    -- 0 initial
    theorem zero_initial
      {x : ℕ}
      : 0 ≤ x
      := by
        exists x
        exact (@add.lem_0_add x).symm
  end le

  def lt (x : ℕ) (y : ℕ) : Prop := ∃ (δ : ℕ), y = x + δ ∧ δ ≠ 0
  instance : LT ℕ where lt := ℕ.lt
  namespace lt
    theorem ntn : ∀ {x y : ℕ}, x.lt y = (x < y) := rfl

    theorem irrefl : ∀ {x : ℕ}, ¬ (x < x) := by
      intro x ⟨δ, ⟨h_δ, h_δ_ne_0⟩⟩
      conv at h_δ => {
        lhs
        apply (add.lem_add_0 x).symm
      } -- `h_δ : x + 0 = x + δ`
      have h_δ : δ = 0 := Eq.symm $ add.thm_left_cancel x 0 δ h_δ
      contradiction


    theorem succ_lt_strong_hom
      {x y : ℕ}
      : x < y ↔ x.succ < y.succ
      := by
        constructor
        case mp =>
          intro ⟨δ, h_δ⟩
          have : δ ≠ 0 := h_δ.right
          have : y.succ = x.succ + δ := calc y.succ
            _ = (x + δ).succ  := by rw [h_δ.left]
            _ = x.succ + δ    := by rw [add.lem_succ_add]
          exists δ
        case mpr =>
          intro ⟨δ, h_δ⟩
          have : δ ≠ 0 := h_δ.right
          have : y.succ = (x + δ).succ := calc y.succ
            _ = x.succ + δ    := h_δ.left
            _ = (x + δ).succ  := by rw [add.lem_succ_add]
          have : y = x + δ := by injection this
          exists δ

    theorem trichotomy
      (x y : ℕ)
      : x < y ∨ x = y ∨ x > y :=
        match x, y with
        | 0, 0 => .inr (.inl rfl)
        | 0, succ y => .inl $ by
          exists y.succ
          constructor
          · exact (add.lem_0_add y.succ).symm
          · intro h ; injection h
        | succ x, 0 => .inr ∘ .inr $ by
          exists x.succ
          constructor
          · exact (add.lem_0_add x.succ).symm
          · intro h ; injection h
        | succ x, succ y =>
          match trichotomy x y with
          | .inl h_x_lt_y => .inl $ succ_lt_strong_hom.mp h_x_lt_y
          | .inr (.inl h_x_eq_y) => .inr ∘ .inl $ congrArg succ h_x_eq_y
          | .inr (.inr h_x_gt_y) => .inr ∘ .inr $ succ_lt_strong_hom.mp h_x_gt_y
  end lt

  namespace order
    theorem le_iff_lt_v_eq
      {x y : ℕ}
      : x ≤ y
      ↔ x < y ∨ x = y
      := by
        constructor
        case mp =>
          intro ⟨δ, h_δ⟩
          cases δ with
          | zero =>
            conv at h_δ => {
              rhs ; rhs ;
              rw [ntn_zero_eq_0]
            }
            have h_δ : x = y := h_δ.symm
            exact Or.inr h_δ
          | succ δ =>
            apply Or.inl
            exists δ.succ
            constructor
            · assumption
            · intro h ; injection h
        case mpr =>
          intro h
          cases h with
          | inl h =>
            let ⟨δ, h_δ⟩ := h
            let h_δ := h_δ.left
            exists δ
          | inr h =>
            rw [h]
            exact le.refl
    theorem lt_iff_le_and_neq
      {x y : ℕ}
      : x < y
      ↔ x ≤ y
      ∧ x ≠ y
      := by
        constructor
        case mp =>
          intro ⟨δ, h_δ⟩
          constructor
          case left =>
            simp [h_δ]
            apply @le.add_le_add x 0 x δ le.refl le.zero_initial
          case right =>
            simp [h_δ]
            intro h
            have h := Eq.symm $ add.thm_left_cancel x 0 δ h
            have h_δ := h_δ.right
            contradiction
        case mpr =>
          intro ⟨⟨δ, h_δ⟩, h_x_neq_y⟩
          rw [h_δ] at h_x_neq_y
          exists δ
          constructor ; case left => assumption ;
          intro h_δ_eq_0
          rw [h_δ_eq_0, add.lem_add_0] at h_x_neq_y
          contradiction -- `x ≠ x`

    theorem lt_succ_iff_le
      {x y : ℕ}
      : x < succ y
      ↔ x ≤ y
      := by
        constructor
        case mp =>
          intro ⟨δ, ⟨h_δ, h_δ_ne_0⟩⟩
          cases δ ; case zero => contradiction -- assumption `δ = 0` contradicts `h_δ_ne_0 : δ ≠ 0`
          case succ δ =>
          rw [add.lem_add_succ] at h_δ ; injection h_δ with h
          exists δ
        case mpr =>
          intro ⟨δ, h_δ⟩
          exists succ δ
          constructor
          case right => intro h ; injection h
          case left => rw [h_δ] ; rfl
  end order

  namespace lt
    theorem lem_zero_acc
      : Acc ℕ.lt 0
      := by
        constructor
        intro y ⟨δ, ⟨h_0_eq_y_δ, (h_δ_ne_0 : δ ≠ 0)⟩⟩ -- `δ ≠ 0` proven here
        have h_δ_eq_0 : δ = 0 := And.right $ ℕ.add.thm_args_0_of_add_0 h_0_eq_y_δ.symm -- `δ = 0` proven here
        contradiction
    theorem lem_succ_acc
      (x : ℕ)
      (h_x_acc : Acc ℕ.lt x)
      : Acc ℕ.lt (succ x)
      := by
        constructor
        have h_all_under_x_acc : ∀ (z : ℕ), z < x → Acc ℕ.lt z := match h_x_acc with | Acc.intro x h => h
        intro y (h_y_lt_succ_x : y < succ x)
        have h := order.le_iff_lt_v_eq.mp ∘ order.lt_succ_iff_le.mp $ h_y_lt_succ_x
        cases h
        case inr h_y_eq_x => rw [h_y_eq_x] ; assumption
        case inl h_y_lt_x => apply h_all_under_x_acc ; assumption

    theorem thm_lt_well_founded
      : WellFounded ℕ.lt
      := by
        constructor
        intro x ; induction x
        case h.zero => exact lem_zero_acc
        case h.succ x ih => exact lem_succ_acc x ih
  end lt

  namespace le
    theorem le_succ :
      ∀ {x : ℕ}, x ≤ x.succ
      := by
        intro x
        exists 1

    theorem ge_1_of_ne_0
      {x : ℕ}
      : x ≠ 0
      → 1 ≤ x
      := by
        intro h_x_ne_0
        match x with
        | 0 => contradiction
        | succ x =>
          have : x.succ = x + 1 := rfl
          rw [this]
          have : (1 : ℕ) = 0 + 1 := rfl
          rw [this]
          apply le.add_le_add
          · exact zero_initial
          · exists 0
    theorem ne_0_of_1_le
      {x : ℕ}
      : 1 ≤ x
      → x ≠ 0
      := by
        intro ⟨δ, h_δ⟩
        match x with
        | 0 =>
          have : (1 : ℕ) = 0 := And.left $ add.thm_args_0_of_add_0 h_δ.symm
          contradiction
        | succ x =>
          intro h ; injection h
  end le

  namespace order
    instance : Trans ℕ.le ℕ.lt ℕ.lt where
      trans := by
        intro a b c ⟨δ, h_δ⟩ ⟨ε, h_ε, h_ε_ne_0⟩
        rw [lt.ntn]
        rw [h_δ, ← add.thm_assoc] at h_ε
        exists δ + ε
        constructor
        · assumption
        · -- show a contradiction
          intro h
          have h := add.thm_args_0_of_add_0 h |> And.right
          contradiction
  end order



  -- SECTION: Induction
  namespace induction
    /-- aka. Structural induction. A specified form of the recursor; i.e. the recursor is *stronger*. -/
    theorem vanilla_induction
      (P : ℕ → Prop)
      (h_0 : P 0)
      (ih : ∀ (x : ℕ), P x → P (succ x))
      : ∀ (x : ℕ), P x
      := @ℕ.rec P h_0 ih

    theorem strong_induction
      (P : ℕ → Prop)
      (h_0 : P 0)
      (sih : ∀ (x : ℕ), (∀ (y : ℕ), y < x → P y) → P x)
      : ∀ (x : ℕ), P x
      :=
        -- `lemma` is to be proven (vanilla) inductively (in `b`).
        -- It mirrors the form of the strong hypothesis.
        have lemma : ∀ (b : ℕ), (∀ (x : ℕ), x ≤ b → P x) := by
          intro b ; induction b
          case zero =>
            intro x h
            rw [ℕ.ntn_zero_eq_0] at h
            have ⟨δ, h_δ⟩ := h
            have h_x_eq_0 : x = 0 := (add.thm_args_0_of_add_0 h_δ.symm).left
            rw [h_x_eq_0]
            assumption
          case succ b vih =>
            intro x h
            have h := order.le_iff_lt_v_eq.mp h
            cases h
            case inl h =>
              have h := order.lt_succ_iff_le.mp h
              -- `h : x ≤ b`; `vih : ∀ (x : ℕ), x ≤ b → P x` applies
              exact vih x h
            case inr h =>
              rw [h]
              apply sih
              intro y h
              have h := order.lt_succ_iff_le.mp h
              exact vih y h
        -- A straightforward application of the lemma finishes the proof
        fun x =>
        lemma (succ x) x le.le_succ

    /-- Every inhabited subset of `ℕ` has a least element. This proof uses Classical logic. -/
    theorem well_ordering_principle
      (S : ℕ → Prop)
      (h_S_nonempty : ∃ (s : ℕ), S s)
      : ∃ (m : ℕ),
        S m ∧ ∀ (s : ℕ), S s → m ≤ s
      := by
        have lemma : ∀ (e : ℕ), S e → ∃ (m : ℕ), S m ∧ (∀ (s : ℕ), S s → m ≤ s) := by
          apply strong_induction
          case h_0 => -- Base case
            intro h
            exists 0
            constructor
            · assumption
            · intro s h
              exact le.zero_initial
          case sih =>
            intro x sih h_x
            cases Classical.em $ ∃ (y : ℕ), y < x ∧ S y
            case inl h => -- Case where there is a smaller element of `S` than `x`
              have ⟨y, h⟩ := h
              apply sih y h.left h.right
            case inr h => -- Case where there is no smaller element of `S` than `x`
            exists x
            constructor
            · assumption
            · intro s h_s
              apply Classical.byContradiction
              intro h_n_x_le_s
              apply h
              exists s
              constructor ; case right => assumption
              case left =>
                show s < x
                have h_trichotomous := lt.trichotomy s x ; cases h_trichotomous
                · assumption
                case inr h_trichotomous =>
                  cases h_trichotomous
                  case inl h_s_eq_x =>
                    -- Find a contradiction
                    rw [h_s_eq_x] at h_n_x_le_s
                    have : False := h_n_x_le_s le.refl
                    contradiction
                  case inr h_s_gt_x =>
                    -- Find a contradiction
                    have ⟨δ, h_δ⟩ := h_s_gt_x
                    have h_x_le_s : x ≤ s := by exists δ ; exact h_δ.left
                    contradiction
        -- Straightforward application of the lemma
        have ⟨e, h_e⟩ := h_S_nonempty
        exact lemma e h_e

    theorem vanilla_induction_from
      (start : ℕ)
      (P : ℕ → Prop)
      (h_start : P start)
      (ih : ∀ (x : ℕ), start ≤ x → P x → P (succ x))
      : ∀ (x : ℕ), start ≤ x → P x
      :=
        let Q : ℕ → Prop := (P $ start + ·)
        have : ∀ (x : ℕ), Q x :=
          vanilla_induction Q h_start $
          fun x (h : P (start + x)) =>
          suffices P (start + x).succ by simp [Q] ; assumption
          by
            apply ih (start + x)
            · apply le.le_add_right
            · assumption
        fun x ⟨δ, h_δ⟩ =>
        by
          rw [h_δ]
          show Q δ
          apply this

    theorem strong_induction_from
      (start : ℕ)
      (P : ℕ → Prop)
      (h_start : P start)
      (ih : ∀ (x : ℕ), start ≤ x → (∀ (y : ℕ), start ≤ y → y < x → P y) → P x)
      : ∀ (x : ℕ), start ≤ x → P x
      := by
        let Q : ℕ → Prop := fun x => P $ start + x
        have : ∀ (x : ℕ), Q x :=
          strong_induction Q h_start $
          fun x' h' =>
          ih (start + x') le.le_add_right $
          fun y ⟨δ, h_δ⟩ h_y_lt_start_x' => by
          rw [h_δ] ; rw [h_δ] at h_y_lt_start_x'
          apply h' δ
          let ⟨ε, ⟨h_ε, h_ε'⟩⟩ := h_y_lt_start_x'
          rw [←add.thm_assoc] at h_ε
          have h_ε := add.thm_left_cancel start _ _ h_ε
          exists ε
        intro x ⟨δ, h_δ⟩
        rw [h_δ]
        apply this
  end induction



  -- SECTION: Fundamental Theorem of Arithmetic
  namespace fund_arithmetic
    /-- The divisibility relationship on ℕ. Uses unicode `∣` (type with `\|`) rather than ascii `|` (type with `|`). -/
    def divides (d : ℕ) (x : ℕ) : Prop := ∃ (q : ℕ), x = d * q
    @[inherit_doc] infix:50 " ∣ " => divides

    theorem le_of_divides
      {d x : ℕ}
      : x ≠ 0
      → d ∣ x
      → d ≤ x
      := by
        intro h_x_ne_0 ⟨q, h_q⟩
        have h_trich := lt.trichotomy d x
        cases h_trich
        case inl h_trich =>
          have ⟨δ, ⟨_, _⟩⟩ := h_trich
          exists δ
        case inr h_trich =>
          cases h_trich
          case inl h_d_eq_x => rw [h_d_eq_x] ; exists 0
          case inr h_x_lt_d =>
            -- show a contradiction
            have ⟨δ, ⟨h_δ, h_δ_ne_0⟩⟩ := h_x_lt_d
            rw [h_δ, mul.thm_add_mul] at h_q
            match q with
            | 0 =>
              -- show a contradiction
              have h_q : x = 0 := h_q
              contradiction -- with `h_x_ne_0 : x ≠ 0`
            | succ q =>
              -- show a contradiction
              have h_q : 0 + x = x * q + δ * q + δ + x :=
                calc 0 + x
                  _ = x := by rw [add.lem_0_add]
                  _ = x * q.succ + δ * q.succ := h_q
                  _ = (x * q + x) + (δ * q + δ) := rfl
                  _ = ((x * q + x) + δ * q) + δ := by rw [add.thm_assoc]
                  _ = (x * q + (x + δ * q)) + δ := by rw [← add.thm_assoc (x * q)]
                  _ = (x * q + (δ * q + x)) + δ := by rw [add.thm_comm x]
                  _ = ((x * q + δ * q) + x) + δ := by rw [add.thm_assoc (x * q)]
                  _ = (x * q + δ * q) + (x + δ) := by rw [← add.thm_assoc]
                  _ = (x * q + δ * q) + (δ + x) := by rw [add.thm_comm x]
                  _ = ((x * q + δ * q) + δ) + x := by rw [← add.thm_assoc (x * q + δ * q)]
              have h_q : 0 = x * q + δ * q + δ := add.thm_right_cancel x _ _ h_q
              have : δ = 0 := And.right $ add.thm_args_0_of_add_0 h_q.symm
              contradiction -- with `h_δ_ne_0 : δ ≠ 0`

    def prime (p : ℕ) : Prop := p ≠ 1 ∧ ∀ (d : ℕ), d ∣ p → d = 1 ∨ d = p
    def composite (x : ℕ) : Prop := x = 1 ∨ ∃ (d : ℕ), d ≠ 1 ∧ d ≠ x ∧ d ∣ x

    /-- Proof that any nonzero number is either prime or composite. -/
    theorem lem_composite_of_n_prime
      : ∀ (x : ℕ),
        x ≠ 0
        → ¬ (prime x)
        → composite x
      := by
        intro x h_x_ne_0 h_n_prime_x
        have h_n_prime_x : x = 1 ∨ ∃ (d : ℕ), d ∣ x ∧ d ≠ 1 ∧ d ≠ x := by -- painful logic rewriting
          rw [(calc ¬ prime x
            _ = ¬ (x ≠ 1 ∧ ∀ (d : ℕ), d ∣ x → d = 1 ∨ d = x)          := rfl
            _ = (¬ (x ≠ 1) ∨ ¬ ∀ (d : ℕ), d ∣ x → d = 1 ∨ d = x)      := by rw [Classical.not_and_iff_or_not_not]
            _ = (x = 1 ∨ ¬ ∀ (d : ℕ), d ∣ x → d = 1 ∨ d = x)          := by
                                                                        have : (¬ (x ≠ 1)) = (x = 1) := Classical.not_not |> propext
                                                                        rw [this]
            _ = (x = 1 ∨ ∃ (d : ℕ), ¬ (d ∣ x → d = 1 ∨ d = x))        := by rw [Classical.not_forall]
            _ = (x = 1 ∨ ∃ (d : ℕ), d ∣ x ∧ ¬ (d = 1 ∨ d = x))        := by conv => {
                                                                          lhs ; rhs ; arg 1 ; intro d
                                                                          rw [not_imp]
                                                                        }
            _ = (x = 1 ∨ ∃ (d : ℕ), d ∣ x ∧ (¬ (d = 1) ∧ ¬ (d = x)))  := by conv => {
                                                                          lhs ; rhs ; arg 1 ; intro d ; rhs
                                                                          rw [not_or]
                                                                        }
            _ = (x = 1 ∨ ∃ (d : ℕ), d ∣ x ∧ d ≠ 1 ∧ d ≠ x)            := rfl
          )] at h_n_prime_x ; assumption
        cases h_n_prime_x
        case inl h => rw [h] ; apply Or.inl ; rfl
        case inr h =>
          have ⟨d, h_d⟩ := h
          apply Or.inr
          exists d
          constructor
          · exact h_d.right.left
          · constructor
            · exact h_d.right.right
            · exact h_d.left

    theorem lem_foldr_mul_bad_base
      {xs : List ℕ}
      {b : ℕ}
      : xs.foldr ℕ.mul b
      = xs.foldr ℕ.mul 1 * b
      := match xs with
      | [] => calc [].foldr ℕ.mul b
        _ = b                     := rfl
        _ = 1 * b                 := by rw [mul.lem_1_mul]
        _ = [].foldr ℕ.mul 1 * b  := rfl
      | (x :: xs) =>
        calc (x :: xs).foldr ℕ.mul b
          _ = x * xs.foldr ℕ.mul b        := by apply List.foldr_cons
          _ = x * (xs.foldr ℕ.mul 1 * b)  := by rw [@lem_foldr_mul_bad_base xs]
          _ = (x * xs.foldr ℕ.mul 1) * b  := by rw [mul.thm_assoc]
          _ = (x :: xs).foldr ℕ.mul 1 * b := by rw [←mul.ntn (x := x), (List.foldr_cons xs (f := ℕ.mul) (b := 1) (a := x)).symm] -- evil

    /-- Existence part of the fundamental theorem of arithmetic. No constraint that the list of primes be ascending. -/
    theorem lem_fund_arith_exists
      (x : ℕ)
      (h_x_ne_0 : x ≠ 0)
      : ∃ (ps : List ℕ),
        (∀ (p : ℕ), p ∈ ps → prime p)
        ∧ x = ps.foldr ℕ.mul 1
      := by
        apply induction.strong_induction_from 1 (fun x => ∃ (ps : List ℕ), (∀ (p : ℕ), p ∈ ps → prime p) ∧ x = ps.foldr ℕ.mul 1)
        case a =>
          show 1 ≤ x
          exact le.ge_1_of_ne_0 h_x_ne_0
        case h_start =>
          exists []
          apply And.intro
          case left =>
            show ∀ (p : ℕ), p ∈ [] → prime p
            intro _ h ; cases h -- trivial
          case right =>
            show 1 = [].foldr ℕ.mul 1
            rfl
        case ih =>
          intro x h_1_le_x ih
          by_cases h : prime x
          case pos => -- Assuming `h : prime x`
            exists [x]
            apply And.intro
            case left =>
              show ∀ (p : ℕ), p ∈ [x] → prime p
              intro p h ; cases h
              case head => assumption
              case tail h => cases h -- ends in contradiction
            case right =>
              apply Eq.symm
              show [x].foldr ℕ.mul 1 = x
              calc [x].foldr ℕ.mul 1
                _ = x * 1 := rfl
                _ = x := mul.lem_mul_1 x
          case neg => -- Assuming `h : ¬ prime x`
            show ∃ ps, (∀ (p : ℕ), p ∈ ps → prime p) ∧ x = ps.foldr ℕ.mul 1
            have h : composite x := lem_composite_of_n_prime x (le.ne_0_of_1_le h_1_le_x) h
            -- x = 1 ∨ ∃ (d : ℕ), d ≠ 1 ∧ d ≠ x ∧ d ∣ x
            cases h
            case inl h =>
              exists []
              constructor
              · intro p h ; cases h
              · calc x
                  _ = x * 1                 := by rw [mul.lem_mul_1]
                  _ = x * [].foldr ℕ.mul 1  := rfl
                rw [h, mul.lem_1_mul]
            case inr h =>
              have ⟨d, ⟨h_d_ne_1, h_d_ne_x, ⟨q, h_q⟩⟩⟩ := h
              show ∃ ps, (∀ (p : ℕ), p ∈ ps → prime p) ∧ x = List.foldr mul 1 ps
              -- We recurse onto the factors `d` and `q` of `x` (thanks to `ih`), and
              --  build a witness for `ps` by taking recursive witnesses `ds` from `d`
              --  and `qs` from `q`, and concatenating them.
              have h_1_le_d : 1 ≤ d := by
                match d with
                | 0 =>
                  show 1 ≤ 0
                  rw [mul.lem_0_mul] at h_q
                  rw [h_q] at h_1_le_x
                  exact h_1_le_x
                | succ d =>
                  show 1 ≤ d.succ
                  exists d
                  rw [add.thm_comm 1, add.lem_succ_eq_add_1]
              have h_1_le_q : 1 ≤ q := by -- virtually the same proof as `h_1_le_d`
                match q with
                | 0 =>
                  show 1 ≤ 0
                  rw [mul.lem_mul_0] at h_q
                  rw [h_q] at h_1_le_x
                  exact h_1_le_x
                | succ q =>
                  show 1 ≤ q.succ
                  exists q
                  rw [add.thm_comm 1, add.lem_succ_eq_add_1]
              have h_x_ne_0 : x ≠ 0 := le.ne_0_of_1_le h_1_le_x
              have h_d_lt_x : d < x := by
                have : d ≤ x := le_of_divides h_x_ne_0 ⟨q, h_q⟩
                have : d < x ∨ d = x := order.le_iff_lt_v_eq.mp this
                cases this
                case inl => assumption
                case inr => contradiction -- `d = x` and `d ≠ x`
              have h_q_lt_x : q < x := by -- virtually the same proof as `h_d_lt_x`
                have : q ≤ x := le_of_divides h_x_ne_0 ⟨d, (by rw [mul.thm_comm] at h_q ; exact h_q)⟩
                have : q < x ∨ q = x := order.le_iff_lt_v_eq.mp this
                cases this
                case inl => assumption
                case inr h_q_eq_x =>
                  -- Somewhat more involved contradiction. Could've symmetrised the arguments among `d` and `q` to make this proof entirely isomorphic to the one for `d`.s
                  rw [h_q_eq_x] at h_q
                  conv at h_q => {
                    lhs
                    rw [← mul.lem_1_mul x]
                  }
                  have h_d_eq_1 := mul.thm_right_cancel x d 1 (by assumption) h_q.symm
                  contradiction -- with `d ≠ 1`
              have ⟨ds, h_ds⟩ := ih d h_1_le_d h_d_lt_x
              have ⟨qs, h_qs⟩ := ih q h_1_le_q h_q_lt_x
              exists ds ++ qs
              show (∀ (p : ℕ), p ∈ ds ++ qs → prime p) ∧ x = List.foldr mul 1 (ds ++ qs)
              apply And.intro
              case left =>
                show (∀ (p : ℕ), p ∈ ds ++ qs → prime p)
                intro p h
                have h := List.mem_append.mp h
                have h_ds := h_ds.left p
                have h_qs := h_qs.left p
                cases h <;> (rename_i h ; first | apply h_ds ; assumption | apply h_qs ; assumption)
              case right =>
                apply Eq.symm
                show (ds ++ qs).foldr ℕ.mul 1 = x
                have h_ds := h_ds.right.symm
                have h_qs := h_qs.right.symm
                rw [List.foldr_append ℕ.mul 1 ds qs, h_qs]
                rw [lem_foldr_mul_bad_base, h_ds, h_q]

    def list_increasing : List ℕ → Prop
      | []              => True
      | (_ :: [])       => True
      | (a :: b :: xs)  => a ≤ b ∧ list_increasing (b :: xs)

    /-- Euclidean (quotient-remainder) division on ℕ. Both the existence and uniqueness statements are here. -/
    theorem euclidean_division
      (x d : ℕ)
      (h_d_ne_0 : d ≠ 0)
      : (∃ (q r : ℕ),
        x = d * q + r
        ∧ r < d)
      ∧ ∀ (q q' r r' : ℕ),
        x = d * q + r ∧ x = d * q' + r'
        ∧ r < d       ∧ r' < d
        → q = q' ∧ r = r'
      := by
        revert x
        apply induction.strong_induction
        case h_0 => -- Base case
          constructor
          case left =>
            show ∃ q r, 0 = d * q + r ∧ r < d
            exists 0 ; exists 0
            constructor
            · rfl
            · match d with | 0 => contradiction | succ d => {
                rw [order.lt_succ_iff_le]
                exact le.zero_initial
              }
          case right =>
            show ∀ (q q' r r' : ℕ), 0 = d * q + r ∧ 0 = d * q' + r' ∧ r < d ∧ r' < d → q = q' ∧ r = r'
            -- Will show that `q = q' = r = r' = 0`.
            have lemma : ∀ (q r : ℕ), 0 = d * q + r → q = 0 ∧ r = 0 := by
              intro q r h_qr
              have ⟨h_q, h_r_eq_0⟩ := add.thm_args_0_of_add_0 h_qr.symm
              rw [← mul.lem_mul_0 d] at h_q
              have h_q_eq_0 := mul.thm_left_cancel d q 0 h_d_ne_0 h_q
              constructor <;> assumption
            -- Straightforward application of the lemma
            intro q q' r r' ⟨h_qr, h_q'r', _, _⟩
            have ⟨h_q_eq_0, h_r_eq_0⟩ := lemma q r h_qr
            have ⟨h_q'_eq_0, h_r'_eq_0⟩ := lemma q' r' h_q'r'
            rw [h_q_eq_0, h_r_eq_0, h_q'_eq_0, h_r'_eq_0]
            constructor <;> rfl
        case sih =>
          intro x ih
          have h := lt.trichotomy x d
          have h : x < d ∨ d ≤ x := by
            rw [@or_comm (x = d) (x > d), gt_iff_lt, Eq.comm, ← order.le_iff_lt_v_eq] at h
            assumption
          cases h
          case inl h => -- Case where `x < d`; base case
            apply And.intro
            case left =>
              show ∃ q r, x = d * q + r ∧ r < d
              exists 0 ; exists x
              constructor
              · rw [mul.lem_mul_0, add.lem_0_add]
              · exact h
            case right =>
              -- Will show `q = q' = 0` and `r = r' = x`
              have lemma : ∀ (q r : ℕ), x = d * q + r → q = 0 ∧ r = x := by
                intro q r h_qr
                have h_q_eq_0 : q = 0 := by
                  rw [h_qr] at h
                  match q with | 0 => rfl | succ q => {
                    -- show a contradiction
                    rw [mul.lem_mul_succ, add.thm_comm _ d] at h
                    have ⟨δ, h_δ, h_δ_ne_0⟩ := h
                    -- Our contradiction will be `: δ = 0`, contradicting `h_δ_ne_0 : δ ≠ 0`
                    conv at h_δ => { lhs; rw [← add.lem_add_0 d] }
                    rw [← add.thm_assoc, ← add.thm_assoc] at h_δ
                    have h_δ := add.thm_left_cancel _ _ _ h_δ
                    rw [add.thm_assoc] at h_δ
                    have : δ = 0 := add.thm_args_0_of_add_0 h_δ.symm |> And.right
                    contradiction
                  }
                apply And.intro
                case left => show q = 0 ; assumption
                case right =>
                  show r = x
                  rw [h_q_eq_0, mul.lem_mul_0, add.lem_0_add] at h_qr
                  apply Eq.symm ; assumption
              intro q q' r r' ⟨h_qr, h_q'r', _, _⟩
              have ⟨h_q_eq_0, h_r_eq_x⟩ := lemma q r h_qr
              have ⟨h_q'_eq_0, h_r'_eq_x⟩ := lemma q' r' h_q'r'
              rw [h_q_eq_0, h_r_eq_x, h_q'_eq_0, h_r'_eq_x]
              constructor <;> rfl
          case inr h => -- Case where `d ≤ x`; recursive case
            have ⟨δ, h_δ⟩ := h
            apply And.intro
            case left =>
              show ∃ q r, x = d * q + r ∧ r < d
              -- Get candidate `q` and `r` by bootstrapping off those for `δ`
              have : δ ≤ x := by
                exists d
                rw [add.thm_comm]
                assumption
              have : δ < x := by
                have : δ < x ∨ δ = x := order.le_iff_lt_v_eq.mp this
                cases this
                case inl => assumption
                case inr this =>
                  -- show a contradiction
                  rw [this] at h_δ
                  conv at h_δ => { lhs ; rw [← add.lem_0_add x] }
                  have h_δ := add.thm_right_cancel x _ _ h_δ |> Eq.symm
                  contradiction
              have ⟨ih_ex, ih_uq⟩ := ih δ this
              have ⟨q, r, h_δ_qr, h_r_lt_d⟩ := ih_ex
              exists q + 1 ; exists r
              show x = d * (q + 1) + r ∧ r < d
              rw [h_δ]
              constructor ; (case right => assumption) ; case left =>
                rw [h_δ_qr, add.thm_assoc, add.thm_comm d, ←mul.lem_mul_succ, add.lem_succ_eq_add_1]
            case right =>
              intro q q' r r' ⟨h_qr, h_q'r', h_r_lt_d, h_r'_lt_d⟩
              -- Rule out `q = 0`
              match q with
              | 0 =>
                -- show a contradiction
                rw [mul.lem_mul_0, add.lem_0_add] at h_qr
                rw [h_qr] at h -- `h : d ≤ r` should now contradict `h_r_lt_d : r < d`
                have : d < d := calc d
                  ℕ.le _ r := h
                  ℕ.lt _ d := h_r_lt_d
                have : ¬ (d < d) := lt.irrefl
                contradiction
              | succ q =>
                -- Rule out `q' = 0`
                match q' with
                | 0 =>
                  -- show a contradiction; same proof as last time
                  rw [mul.lem_mul_0, add.lem_0_add] at h_q'r'
                  rw [h_q'r'] at h
                  have : d < d := calc d
                    ℕ.le _ r' := h
                    ℕ.lt _ d := h_r'_lt_d
                  have : ¬ (d < d) := lt.irrefl
                  contradiction
                | succ q' =>
                  -- Know `q ≠ 0` and `q' ≠ 0`
                  rw [h_δ, mul.lem_mul_succ, add.thm_comm _ d, ← add.thm_assoc] at h_qr
                  have h_qr := add.thm_left_cancel d _ _ h_qr
                  rw [h_δ, mul.lem_mul_succ, add.thm_comm _ d, ← add.thm_assoc] at h_q'r'
                  have h_q'r' := add.thm_left_cancel d _ _ h_q'r'
                  have h_δ_lt_x : δ < x := by
                    exists d
                    constructor
                    · rw [add.thm_comm] ; assumption
                    · assumption
                  have ih := (ih δ h_δ_lt_x).right q q' r r'
                  have ⟨h_q_eq_q', h_r_eq_r'⟩ := ih ⟨(by assumption), (by assumption), (by assumption), (by assumption)⟩ -- lmao
                  rw [h_q_eq_q', h_r_eq_r']
                  constructor <;> rfl

    theorem prime_divides_product
      {p a b : ℕ}
      : prime p
      → p ∣ a * b
      → p ∣ a ∨ p ∣ b
      := sorry -- FIXME:

    theorem prime_divides_product_list
      {p : ℕ} {qs : List ℕ}
      : prime p
      → (∀ (q : ℕ), q ∈ qs → prime q)
      → p ∣ qs.foldr ℕ.mul 1
      → p ∈ qs
      := by
        induction qs
        case nil =>
          intro h_prime_p h_prime_qs ⟨d, h_d⟩
          -- show a contradiction
          have h_d : p * d = 1 := h_d.symm
          have : p = 1 := And.left $ mul.thm_args_1_of_mul_1 _ _ h_d
          have : p ≠ 1 := h_prime_p.left
          contradiction
        case cons q qs ih =>
          intro h_prime_p h_prime_qs ⟨d, h_d⟩
          show p ∈ q :: qs
          have : (q :: qs).foldr mul 1 = q * qs.foldr mul 1 := by apply List.foldr_cons
          rw [this] at h_d
          have : p ∣ q * qs.foldr mul 1 := by exists d
          have : p ∣ q ∨ p ∣ qs.foldr mul 1 := prime_divides_product (by assumption) this
          cases this
          case inr =>
            rw [List.mem_cons]
            apply Or.inr
            apply ih
            · assumption
            · intro q h_q_in_qs
              apply h_prime_qs q
              rw [List.mem_cons] ; apply Or.inr ; assumption
            · assumption
          case inl h_p_divides_q =>
            have : prime q := by
              apply h_prime_qs q
              rw [List.mem_cons]
              exact Or.inl rfl
            unfold prime at this
            have : p = 1 ∨ p = q := this.right p h_p_divides_q
            cases this
            case inl h_p_eq_1 =>
              have : p ≠ 1 := h_prime_p.left
              contradiction
            case inr h_p_eq_q =>
              rw [h_p_eq_q]
              apply List.mem_cons.mpr ; apply Or.inl ; rfl

    /--
      Uniqueness part of the fundamental theorem of arithmetic.
      Actual uniqueness of the list of primes (not uniqueness up to permutation) is
        enforced by requiring it to be sorted.
    -/
    theorem lem_fund_arith_unique
      (x : ℕ)
      (h_x_ne_0 : x ≠ 0)
      : ∀ (ps qs : List ℕ),
        (∀ (p : ℕ), p ∈ ps → prime p) ∧ (∀ (q : ℕ), q ∈ qs → prime q)
        ∧ x = ps.foldr ℕ.mul 1        ∧ x = qs.foldr ℕ.mul 1
        ∧ list_increasing ps          ∧ list_increasing qs
        → qs = ps
      := sorry -- FIXME:

    /--
      The fundamental theorem of arithmetic; any nonzero natural number has a unique-up-to-permutation
        factorisation into primes.
      Uniqueness-up-to-permutation is encoded as requring that a *sorted* list of prime factors be
        unique.
    -/
    theorem fund_arith
      (x : ℕ)
      (h_x_ne_0 : x ≠ 0)
      : (∃ (ps : List ℕ),
        (∀ (p : ℕ), p ∈ ps → prime p)
        ∧ x = ps.foldr ℕ.mul 1
      ) ∧ ∀ (ps qs : List ℕ),
        (∀ (p : ℕ), p ∈ ps → prime p) ∧ (∀ (q : ℕ), q ∈ qs → prime q)
        ∧ x = ps.foldr ℕ.mul 1        ∧ x = qs.foldr ℕ.mul 1
        ∧ list_increasing ps          ∧ list_increasing qs
        → qs = ps
      := by
        constructor
        · exact lem_fund_arith_exists x h_x_ne_0
        · exact lem_fund_arith_unique x h_x_ne_0
  end fund_arithmetic

end ℕ

end Numbers
