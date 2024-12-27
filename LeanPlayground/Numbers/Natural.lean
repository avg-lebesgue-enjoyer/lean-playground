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
          case right => simp
          rw [h_δ, add.lem_add_succ]
  end order

  namespace lt
    -- TODO: Show `WellFounded`ness of `<`
    /-
    inductive Acc.{u} : {α : Sort u} → (α → α → Prop) → α → Prop
    number of parameters: 2
    constructors:
    `Acc.intro : ∀ {α : Sort u} {r : α → α → Prop} (x : α), (∀ (y : α), r y x → Acc r y) → Acc r x`
    -/
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
  end le



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

    theorem well_ordering_principle
      (S : ℕ → Prop)
      (h_S_nonempty : ∃ (s : ℕ), S s)
      : ∃ (m : ℕ),
        S m ∧ ∀ (s : ℕ), S s → m ≤ s
      := sorry -- FIXME:

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

end ℕ

end Numbers
