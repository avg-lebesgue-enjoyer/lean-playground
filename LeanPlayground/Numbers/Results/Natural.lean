/- @file LeanPlayground/Numbers/Results/Natural.lean
 - Results proven about the natural numbers ℕ
 -/

/- IMPORTS: The natural numbers -/
import LeanPlayground.Numbers.Natural



/- LAUNCH: Results -/
namespace Numbers.ℕ.results

  -- SECTION: Notation
  @[simp] theorem ntn.zero_eq_0 : zero = 0 := ntn_zero_eq_0
  @[simp] theorem ntn.succ_zero_eq_1 : succ zero = 1 := ntn_succ_zero_eq_1
  @[simp] theorem ntn.add {x y : ℕ} : x.add y = x + y := add.ntn
  @[simp] theorem ntn.mul {x y : ℕ} : x.mul y = x * y := mul.ntn
  @[simp] theorem ntn.le : ∀ {x y : ℕ}, x.le y = (x ≤ y) := le.ntn
  @[simp] theorem ntn.lt : ∀ {x y : ℕ}, x.lt y = (x < y) := lt.ntn



  -- SECTION: Induction and Well-Ordering
  #check ℕ.rec



  -- SECTION: Successor
  namespace constructors
    def succ_inj {x y : ℕ} : x.succ = y.succ → x = y := succ.inj
    def zero_not_succ {x : ℕ} : x.succ ≠ 0 := succ.zero_not_succ x
  end constructors



  -- SECTION: Addition
  namespace arithmetic
    open add
    @[simp] theorem add_zero {x : ℕ} : x + 0 = x := lem_add_0 x
    @[simp] theorem add_succ {x y : ℕ} : x + succ y = succ (x + y) := lem_add_succ x y
    @[simp] theorem zero_add {x : ℕ} : 0 + x = x := lem_0_add x
    @[simp] theorem succ_add {x y : ℕ} : succ x + y = succ (x + y) := lem_succ_add x y

    @[simp] theorem add_assoc {x y z : ℕ} : x + (y + z) = (x + y) + z := thm_assoc x y z
    theorem add_comm (x y : ℕ) : x + y = y + x := thm_comm x y

    theorem args_0_of_add_0 {x y : ℕ} : x + y = 0 → x = 0 ∧ y = 0 := thm_args_0_of_add_0
    theorem arg_1_of_add_1 {x y : ℕ} : x + y = 1 → x = 1 ∨ y = 1 := add.arg_1_of_add_1 x y

    theorem add_right_cancel {c x y : ℕ} : x + c = y + c → x = y := thm_right_cancel c x y
    theorem add_left_cancel {c x y : ℕ} : c + x = c + y → x = y := thm_left_cancel c x y
  end arithmetic

  namespace arithmetic.nosimp
    theorem add_comm (x y : ℕ) : x + y = y + x := arithmetic.add_comm x y

    theorem args_0_of_add_0 {x y : ℕ} : x + y = 0 → x = 0 ∧ y = 0 := arithmetic.args_0_of_add_0
    theorem arg_1_of_add_1 {x y : ℕ} : x + y = 1 → x = 1 ∨ y = 1 := arithmetic.arg_1_of_add_1

    theorem add_right_cancel {c x y : ℕ} : x + c = y + c → x = y := arithmetic.add_right_cancel
    theorem add_left_cancel {c x y : ℕ} : c + x = c + y → x = y := arithmetic.add_left_cancel
  end arithmetic.nosimp



  -- SECTION: Multiplication
  namespace arithmetic
    open mul
    @[simp] theorem mul_zero {x : ℕ} : x * 0 = 0 := lem_mul_0 x
    @[simp] theorem mul_succ {x y : ℕ} : x * succ y = x * y + x := lem_mul_succ x y
    @[simp] theorem zero_mul {x : ℕ} : 0 * x = 0 := lem_0_mul x
    @[simp] theorem succ_mul {x y : ℕ} : succ x * y = x * y + y := lem_succ_mul x y
    @[simp] theorem mul_one {x : ℕ} : x * 1 = x := lem_mul_1 x
    @[simp] theorem one_mul {x : ℕ} : 1 * x = x := lem_1_mul x

    @[simp] theorem mul_assoc {x y z : ℕ} : x * (y * z) = (x * y) * z := thm_assoc x y z
    theorem mul_comm (x y : ℕ) : x * y = y * x := thm_comm x y

    @[simp] theorem mul_add {a x y : ℕ} : a * (x + y) = a * x + a * y := thm_mul_add a x y
    @[simp] theorem add_mul {a b x : ℕ} : (a + b) * x = a * x + b * x := thm_add_mul a b x

    theorem args_1_of_mul_1 {x y : ℕ} : x * y = 1 → x = 1 ∧ y = 1 := thm_args_1_of_mul_1 x y
    theorem arg_0_of_mul_0 {x y : ℕ} : x * y = 0 → x = 0 ∨ y = 0 := thm_arg_0_of_mul_0
    theorem null_factor {x y : ℕ} : x * y = 0 → x = 0 ∨ y = 0 := thm_null_factor

    theorem mul_right_cancel
      {c x y : ℕ}
      : c ≠ 0
      → x * c = y * c
      → x = y
      := thm_right_cancel c x y
    theorem mul_left_cancel
      {c x y : ℕ}
      : c ≠ 0
      → c * x = c * y
      → x = y
      := thm_left_cancel c x y
  end arithmetic

  namespace arithmetic.nosimp
    theorem mul_comm (x y : ℕ) : x * y = y * x := arithmetic.mul_comm x y

    theorem args_1_of_mul_1 {x y : ℕ} : x * y = 1 → x = 1 ∧ y = 1 := arithmetic.args_1_of_mul_1
    theorem arg_0_of_mul_0 {x y : ℕ} : x * y = 0 → x = 0 ∨ y = 0 := arithmetic.arg_0_of_mul_0
    theorem null_factor {x y : ℕ} : x * y = 0 → x = 0 ∨ y = 0 := arithmetic.null_factor

    theorem mul_right_cancel
      {c x y : ℕ}
      : c ≠ 0
      → x * c = y * c
      → x = y
      := arithmetic.mul_right_cancel
    theorem mul_left_cancel
      {c x y : ℕ}
      : c ≠ 0
      → c * x = c * y
      → x = y
      := arithmetic.mul_left_cancel
  end arithmetic.nosimp



  -- SECTION: Order
  namespace order
    open le
    theorem le_refl {x : ℕ} : x ≤ x := refl
    theorem le_antisymm {x y : ℕ} : x ≤ y → y ≤ x → x = y := antisymm
    theorem le_trans {x y z : ℕ} : x ≤ y → y ≤ z → x ≤ z := trans

    theorem le_add_right {x δ : ℕ} : x ≤ x + δ := le.le_add_right
    theorem le_add_left {x δ : ℕ} : x ≤ δ + x := le.le_add_left
    theorem le_add_hom {a b x y : ℕ} : a ≤ x → b ≤ y → a + b ≤ x + y := add_le_add
    theorem le_mul_hom {a b x y : ℕ} : a ≤ x → b ≤ y → a * b ≤ x * y := mul_le_mul

    theorem le_succ_strong_hom {x y : ℕ} : x ≤ y ↔ x.succ ≤ y.succ := succ_le_strong_hom
    theorem le_zero_initial {x : ℕ} : 0 ≤ x := zero_initial
    theorem le_succ {x : ℕ} : x ≤ x.succ := le.le_succ
  end order
  namespace order
    open lt
    theorem lt_irrefl {x : ℕ} : ¬(x < x) := lt.irrefl
    theorem lt_succ_strong_hom {x y : ℕ} : x < y ↔ x.succ < y.succ := succ_lt_strong_hom
    theorem trichotomy : ∀ (x y : ℕ), x < y ∨ x = y ∨ x > y := lt.trichotomy
    theorem lt_well_founded : WellFounded ℕ.lt := thm_lt_well_founded
  end order
  namespace order
    open Numbers.ℕ.order
    theorem le_iff_lt_v_eq {x y : ℕ} : x ≤ y ↔ x < y ∨ x = y := Numbers.ℕ.order.le_iff_lt_v_eq
    theorem lt_iff_le_and_neq {x y : ℕ} : x < y ↔ x ≤ y ∧ x ≠ y := Numbers.ℕ.order.lt_iff_le_and_neq
    theorem lt_succ_iff_le {x y : ℕ} : x < succ y ↔ x ≤ y := Numbers.ℕ.order.lt_succ_iff_le
  end order



  -- SECTION: Induction
  namespace induction
    theorem vanilla_induction
      : (P : ℕ → Prop)
      → P 0
      → (∀ (x : ℕ), P x → P (succ x))
      → ∀ (x : ℕ), P x
      := ℕ.induction.vanilla_induction

    theorem strong_induction
      : (P : ℕ → Prop)
      → P 0
      → (∀ (x : ℕ), (∀ (y : ℕ), y < x → P y) → P x)
      → ∀ (x : ℕ), P x
      := Numbers.ℕ.induction.strong_induction

    theorem well_ordering_principle
      : (S : ℕ → Prop)
      → (∃ (s : ℕ), S s)
      → ∃ (m : ℕ),
        S m
        ∧ ∀ (s : ℕ), S s → m ≤ s
      := ℕ.induction.well_ordering_principle

    theorem vanilla_induction_from
      : (start : ℕ)
      → (P : ℕ → Prop)
      → P start
      → (∀ (x : ℕ), start ≤ x → P x → P (succ x))
      → ∀ (x : ℕ), start ≤ x → P x
      := ℕ.induction.vanilla_induction_from

    theorem strong_induction_from
      : (start : ℕ)
      → (P : ℕ → Prop)
      → P start
      → (∀ (x : ℕ), start ≤ x → (∀ (y : ℕ), start ≤ y → y < x → P y) → P x)
      → ∀ (x : ℕ), start ≤ x → P x
      := ℕ.induction.strong_induction_from
  end induction


  /- SECTION: Results yet to be proven
    [5.] Fundamental Theorem of Arithmetic
      (it)
  -/
end Numbers.ℕ.results
