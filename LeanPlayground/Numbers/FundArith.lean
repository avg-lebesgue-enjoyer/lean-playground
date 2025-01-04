/- @file LeanPlayground/Numbers/FundArith.lean
 - Results building towards the *fundamental theorem of arithmetic*.
 -/

/- IMPORTS: Numbers -/
import LeanPlayground.Numbers.Results.Natural
import LeanPlayground.Numbers.Natural
import LeanPlayground.Numbers.Results.Integer
import LeanPlayground.Numbers.Integer
import LeanPlayground.Numbers.Results.Modular
import LeanPlayground.Numbers.Modular

namespace Numbers.fund_arith
  instance : OfNat ℕ 2 where ofNat := .succ (.succ .zero)
  instance : OfNat ℤ 2 where ofNat := ((2 : ℕ) : ℤ)



  /- SECTION: ¬ prime → composite -/
  theorem solve_eq_two
    {a b : ℕ}
    : a * b = 2
    → (a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
    := match a, b with
    | 0, b => by
      intro h
      rw [ℕ.results.arithmetic.zero_mul] at h
      injection h -- `0 = 2` and `0 ≠ 2`
    | 1, b => by
      intro h
      rw [ℕ.results.arithmetic.one_mul] at h
      apply Or.inr
      constructor
      · rfl
      · assumption
    | 2, b => by
      intro h
      conv at h => { rhs; rw [← @ℕ.results.arithmetic.mul_one 2] }
      have : (2 : ℕ) ≠ 0 := by intro h ; injection h
      have : b = 1 := ℕ.results.arithmetic.mul_left_cancel ‹(2 : ℕ) ≠ 0› h
      apply Or.inl
      constructor
      · rfl
      · assumption
    | .succ (.succ (.succ a)), b => by
      intro (h : a.succ.succ.succ * b = ℕ.zero.succ.succ)
      suffices False by contradiction
      rw  [ ℕ.results.arithmetic.succ_mul
          , ℕ.results.arithmetic.succ_mul
          , ℕ.results.arithmetic.succ_mul
          ] at h
      match b with
      | 0 =>
        rw  [ ℕ.results.arithmetic.add_zero
            , ℕ.results.arithmetic.add_zero
            , ℕ.results.arithmetic.add_zero
            , ℕ.results.arithmetic.mul_zero
            ] at h
        injection h -- `0 = (⋯).succ`
      | .succ b =>
        rw  [ ℕ.results.arithmetic.add_succ
            , ℕ.results.arithmetic.add_right_comm
            , ℕ.results.arithmetic.add_succ
            , ℕ.results.arithmetic.add_right_comm
            , ← ℕ.results.arithmetic.add_right_comm b.succ
            , ← ℕ.results.arithmetic.add_right_comm b.succ
            , ℕ.results.arithmetic.add_succ
            ] at h
        repeat injection h with h
        injection h

  theorem has_prime_factor_of_not_prime
    {x : ℕ}
    : 2 ≤ x
    → ¬ (x : ℤ).prime
    → ∃ (p : ℤ), p.prime ∧ p ∣ x
    := by
      apply ℕ.results.induction.strong_induction_from 2
      · have : (ℤ.mk (2, 0)).prime := by
          unfold ℤ.prime
          constructor
          · rw [gt_iff_lt, ℤ.results.ordered_ring.lt_mk]
            exists 1
            constructor
            · rw  [ ← ℤ.ntn_one
                  , ℤ.results.ring.sub_mk
                  , ℕ.results.arithmetic.add_zero
                  , ℕ.results.arithmetic.zero_add]
              apply ℤ.sound
              show 2 = 1 + 1
              rfl
            · rw [←ℕ.ntn_succ_zero_eq_1]
              intro h ; injection h
          · intro d ⟨q, h_q⟩
            have ⟨d', h_d'⟩ := d.existsCanonRep
            have ⟨q', h_q'⟩ := q.existsCanonRep
            cases h_d'
            case inl h_d' =>
              cases h_q'
              case inl h_q' =>
                rw  [ h_d', h_q', ℤ.results.ring.mul_mk
                    , ℕ.results.arithmetic.mul_zero
                    , ℕ.results.arithmetic.add_zero
                    , ℕ.results.arithmetic.mul_zero
                    , ℕ.results.arithmetic.zero_mul
                    , ℕ.results.arithmetic.add_zero
                    ] at h_q
                have := h_q |> ℤ.exact |> Eq.symm |> solve_eq_two
                cases this
                case inl this =>
                  exists 1
                  constructor
                  · exists 1
                  · apply Or.inl
                    rw [ℤ.results.ring.mul_one, h_d', this.left]
                case inr this =>
                  exists 1
                  constructor
                  · exists 1
                  · apply Or.inr
                    rw [h_d', this.left]
                    rfl
              case inr h_q' =>
                -- show a contradiction
                rw  [ h_d', h_q', ℤ.results.ring.mul_mk
                    , ℕ.results.arithmetic.mul_zero
                    , ℕ.results.arithmetic.zero_add
                    , ℕ.results.arithmetic.zero_mul
                    , ℕ.results.arithmetic.mul_zero
                    , ℕ.results.arithmetic.add_zero
                    ] at h_q
                have h_q : ℕ.zero.succ.succ + d' * q' = 0 := h_q |> ℤ.exact
                rw [ℕ.results.arithmetic.succ_add, ←ℕ.results.ntn.zero_eq_0] at h_q
                injection h_q
            case inr h_d' =>
              cases h_q'
              case inl h_q' =>
                -- show a contradiction
                rw  [ h_d', h_q', ℤ.results.ring.mul_mk
                    , ℕ.results.arithmetic.mul_zero
                    , ℕ.results.arithmetic.zero_mul
                    , ℕ.results.arithmetic.add_zero
                    , ℕ.results.arithmetic.zero_mul
                    , ℕ.results.arithmetic.zero_add
                    ] at h_q
                have h_q : ℕ.zero.succ.succ + d' * q' = 0 := h_q |> ℤ.exact
                rw [ℕ.results.arithmetic.succ_add, ←ℕ.results.ntn.zero_eq_0] at h_q
                injection h_q
              case inr h_q' =>
                rw  [ h_d', h_q', ℤ.results.ring.mul_mk
                    , ℕ.results.arithmetic.mul_zero
                    , ℕ.results.arithmetic.zero_add
                    , ℕ.results.arithmetic.zero_mul
                    , ℕ.results.arithmetic.zero_add
                    , ℕ.results.arithmetic.mul_zero
                    ] at h_q
                have := h_q |> ℤ.exact |> Eq.symm |> solve_eq_two
                cases this
                case inl this =>
                  exists -1
                  constructor
                  · exists -1
                  · apply Or.inl
                    rw [ℤ.results.ring.mul_neg_one, ℤ.results.ring.neg_mk, h_d', this.left]
                case inr this =>
                  exists -1
                  constructor
                  · exists -1
                  · apply Or.inr
                    rw [h_d', this.left]
                    rfl
        intro h
        contradiction -- `2` is prime and `2` is not prime
      · intro x h_2_le_x sih h_n_x_prime
        conv at h_n_x_prime => {
          unfold ℤ.prime
          rw [Classical.not_and_iff_or_not_not]
          rhs
          rw [Classical.not_forall]
          arg 1 ; intro d
          rw [not_imp]
        }
        cases h_n_x_prime
        case a.inl h_x_n_gt_1 =>
          -- show a contradiction
          rw [gt_iff_lt] at h_x_n_gt_1
          have : 1 < ℤ.mk (x, 0) := by
            rw [ℤ.results.ordered_ring.lt_mk]
            have ⟨δ, h_δ⟩ := h_2_le_x
            exists δ + 1
            constructor
            · rw  [ ← ℤ.ntn_one
                  , ℤ.results.ring.sub_mk
                  , ℕ.results.arithmetic.add_zero
                  , ℕ.results.arithmetic.zero_add
                  , h_δ
                  , ℕ.results.arithmetic.add_comm 2]
              apply ℤ.sound
              show δ + 2 = δ + 1 + 1
              rfl
            · rw [← ℕ.results.ntn.succ_zero_eq_1, ℕ.results.arithmetic.add_succ]
              intro h ; injection h
          contradiction -- `1 < x` and `¬ 1 < x`
        case a.inr h =>
          have ⟨d, h_d_div_x, h_d_nontriv_x⟩ := h
          have : ∃ (e : ℕ),
            (e : ℤ) ∣ (x : ℤ)
            ∧ (¬ ∃ (u : ℤ), u.invertible ∧ (e = x * u ∨ e = u))
            ∧ (2 ≤ e)
            := by
              cases ℤ.results.ordered_ring.lt_trichotomy d 0
              case inl h_d_lt_0 =>
                conv at h_d_lt_0 => {
                  rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub]
                  arg 1 ; intro a ; lhs
                  rw [ℤ.results.ring.neg_eq_comm, Eq.comm, ℤ.results.ring.neg_mk]
                }
                have ⟨e, h_e, h_e_ne_0⟩ := h_d_lt_0
                match e with
                | 0 => contradiction -- `0 ≠ 0`
                | 1 =>
                  have : d = -1 := h_e
                  have : (-1 : ℤ).invertible := by exists -1
                  have : ∃ u, u.invertible ∧ (d = ℤ.mk (x, 0) * u ∨ d = u) := by
                    exists -1
                    constructor
                    · assumption
                    · apply Or.inr
                      assumption
                  contradiction -- `∃ u` and `¬ ∃ u`
                | .succ (.succ e) =>
                  exists e.succ.succ
                  constructor
                  · rw [h_e] at h_d_div_x
                    have ⟨q, h_q⟩ := h_d_div_x
                    have ⟨a, b, h_ab⟩ := q.existsRep
                    exists -q
                    rw  [ h_ab
                        , ℤ.results.ring.neg_mk
                        , ℤ.results.ring.mul_mk
                        , ℕ.results.arithmetic.zero_mul
                        , ℕ.results.arithmetic.add_zero
                        , ℕ.results.arithmetic.zero_mul
                        , ℕ.results.arithmetic.add_zero]
                    rw  [ h_ab
                        , ℤ.results.ring.mul_mk
                        , ℕ.results.arithmetic.zero_mul
                        , ℕ.results.arithmetic.zero_add
                        , ℕ.results.arithmetic.zero_mul
                        , ℕ.results.arithmetic.zero_add
                        ] at h_q
                    exact h_q
                  · constructor
                    · intro ⟨u, h_u_inv, h_eu⟩
                      have : ∃ v, v.invertible ∧ (d = x * v ∨ d = v) := by
                        exists -u
                        constructor
                        · have ⟨U, h_U⟩ := ‹u.invertible›
                          exists -U
                          rw [ℤ.results.ring.neg_mul_neg]
                          assumption
                        · rw [← ℤ.results.ring.neg_mk] at h_e
                          rw [h_e]
                          cases h_eu
                          case inl h_eu =>
                            rw [h_eu, ℤ.results.ring.neg_mul_right]
                            apply Or.inl
                            rfl
                          case inr h_eu =>
                            rw [h_eu]
                            apply Or.inr
                            rfl
                      contradiction -- `∃ v` and `¬ ∃ v`
                    · exists e
                      show e.succ.succ = ℕ.zero.succ.succ + e
                      rw  [ ℕ.results.arithmetic.succ_add
                          , ℕ.results.arithmetic.succ_add
                          , ℕ.results.ntn.zero_eq_0
                          , ℕ.results.arithmetic.zero_add]
              case inr h_bich =>
              cases h_bich
              case inl h_d_eq_0 =>
                -- show a contradiction
                rw [‹d = 0›] at h_d_div_x
                have ⟨q, h_q⟩ := h_d_div_x
                rw [ℤ.results.ring.zero_mul, ← ℤ.ntn_zero] at h_q
                have h_q : x = 0 := h_q |> ℤ.exact
                rw [‹x = 0›] at h_2_le_x
                have ⟨δ, (h_δ : ℕ.zero = ℕ.zero.succ.succ + δ)⟩ := h_2_le_x
                rw [ℕ.results.arithmetic.succ_add] at h_δ
                injection h_δ -- contradiction: `ℕ.zero = (⋯).succ`
              case inr h_0_lt_d =>
                rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero] at h_0_lt_d
                have ⟨e, h_e, h_e_ne_0⟩ := h_0_lt_d
                match e with
                | 0 => contradiction -- `0 ≠ 0`
                | 1 =>
                  have : ∃ (u : ℤ), u.invertible ∧ (d = ℤ.mk (x, 0) * u ∨ d = u) := by
                    exists 1
                    constructor
                    · exists 1
                    · apply Or.inr
                      exact h_e
                  contradiction -- `¬ ∃ u` and `∃ u`
                | .succ (.succ e) =>
                  exists e.succ.succ
                  constructor
                  · rw [←h_e]
                    exact h_d_div_x
                  · constructor
                    · rw [← h_e]
                      assumption
                    · exists e
                      show e.succ.succ = ℕ.zero.succ.succ + e
                      rw  [ ℕ.results.arithmetic.succ_add
                          , ℕ.results.arithmetic.succ_add
                          , ℕ.results.ntn.zero_eq_0
                          , ℕ.results.arithmetic.zero_add]
          have ⟨e, h_e_div_x, h_e_nontriv, h_2_le_e⟩ := this
          by_cases (e : ℤ).prime
          case pos =>
            exists e
          case neg =>
            have : e < x := by
              have : 0 < (x : ℤ) := by
                have ⟨δ, h_δ⟩ := h_2_le_x
                rw [ℤ.results.ordered_ring.lt_mk]
                exists δ + 2
                constructor
                · rw [ℤ.results.ring.sub_zero, ℕ.results.arithmetic.add_comm, h_δ]
                · show δ.succ.succ ≠ ℕ.zero
                  intro h ; injection h
              have := ℤ.divisibility.le_of_divides ‹0 < (x : ℤ)› ‹e ∣ (x : ℤ)›
              rw [ℤ.results.ordered_ring.le_iff_lt_or_eq] at this
              cases this
              case inl h_e_lt_x =>
                rw [ℤ.results.ordered_ring.lt_mk] at h_e_lt_x
                have ⟨a, h_a, h_a_ne_0⟩ := h_e_lt_x
                exists a
                constructor
                · rw  [ ℤ.results.ring.sub_mk
                      , ℕ.results.arithmetic.add_zero
                      , ℕ.results.arithmetic.zero_add
                      ] at h_a
                  have : x = a + e := h_a |> ℤ.exact
                  rw [ℕ.results.arithmetic.add_comm]
                  assumption
                · assumption
              case inr h_e_eq_x =>
                have : ∃ u, u.invertible ∧ (ℤ.mk (e, 0) = ℤ.mk (x, 0) * u ∨ ℤ.mk (e, 0) = u) := by
                  exists 1
                  constructor
                  · exists 1
                  · apply Or.inl
                    rw [ℤ.results.ring.mul_one]
                    exact h_e_eq_x
                contradiction -- `∃ u` and `¬ ∃ u`
            have ⟨p, h_p_prime, h_p_div_e⟩ := sih e ‹2 ≤ e› ‹e < x› ‹¬ (e : ℤ).prime›
            exists p
            constructor
            · assumption
            · exact ℤ.results.number_theory.divides_trans ‹p ∣ (e : ℤ)› ‹e ∣ (x : ℤ)›

  theorem pos_of_gt_1 {x : ℤ} : 1 < x → 0 < x := by
    repeat rw [ℤ.results.ordered_ring.lt_mk]
    intro h
    have ⟨a, h_a, h_a_ne_0⟩ := h
    exists a + 1
    rw [ℤ.results.ring.sub_zero]
    apply And.intro
    case left =>
      calc x
        _ = x - 1 + 1 := by rw [ℤ.results.ring.sub_eq_add_neg, ← ℤ.results.ring.add_assoc, ℤ.results.ring.neg_add, ℤ.results.ring.add_zero]
        _ = ℤ.mk (a, 0) + 1     := by rw [h_a]
        _ = ℤ.mk (a + 1, 0)     := by rw [← ℤ.ntn_one, ℤ.results.ring.add_mk, ℕ.results.arithmetic.zero_add]
    case right =>
      intro h; injection h

  theorem mul_pos {x y : ℤ} : 0 < x → 0 < y → 0 < x * y := by
    intro h_x h_y
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero] at h_x
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero] at h_y
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero]
    have ⟨a, h_a, h_a_ne_0⟩ := h_x
    have ⟨b, h_b, h_b_ne_0⟩ := h_y
    exists a * b
    constructor
    · rw  [ h_a, h_b, ℤ.results.ring.mul_mk
          , ℕ.results.arithmetic.mul_zero
          , ℕ.results.arithmetic.add_zero
          , ℕ.results.arithmetic.mul_zero
          , ℕ.results.arithmetic.zero_mul
          , ℕ.results.arithmetic.add_zero]
    · intro h
      cases (ℕ.results.arithmetic.null_factor h) <;> contradiction

  theorem mul_neg_right {x y : ℤ} : 0 < x → y < 0 → x * y < 0 := by
    intro h_x h_y
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero] at h_x
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub] at h_y
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub, ℤ.results.ring.neg_mul_right]
    have ⟨a, h_a, _⟩ := h_x
    have ⟨b, h_b, _⟩ := h_y
    exists a * b
    rw  [ h_a, h_b, ℤ.results.ring.mul_mk
        , ℕ.results.arithmetic.mul_zero
        , ℕ.results.arithmetic.add_zero
        , ℕ.results.arithmetic.mul_zero
        , ℕ.results.arithmetic.zero_mul
        , ℕ.results.arithmetic.add_zero]
    constructor
    · rfl
    · intro h
      cases (ℕ.results.arithmetic.null_factor h) <;> contradiction

  theorem suffering
    {x a b : ℤ}
    : x = a * b
    → 0 < x
    → 1 < a
    → a < x
    → 1 < b ∧ b < x
    := by
      intro h_ab h_0_lt_x h_1_lt_a h_a_lt_x
      have h_1_lt_b : 1 < b := by
        cases ℤ.results.ordered_ring.lt_trichotomy 1 b
        case inl h => assumption
        case inr h =>
        cases h
        case inl h_1_eq_b =>
          rw [‹1 = b›.symm, ℤ.results.ring.spec.mul_one] at h_ab
          rw [h_ab] at h_a_lt_x
          have : ¬ a < a := ℤ.results.ordered_ring.lt_irrefl a
          contradiction -- `a < a`
        case inr h_b_lt_1 =>
          by_cases h : b = 0
          case pos =>
            rw [‹b = 0›, ℤ.results.ring.mul_zero] at h_ab
            rw [h_ab] at h_0_lt_x
            have : ¬ (0 : ℤ) < 0 := ℤ.results.ordered_ring.lt_irrefl 0
            contradiction -- `0 < 0`
          case neg => -- `h : b ≠ 0`
            rw [← ne_eq] at h
            have : b < 0 := by
              rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub]
              rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_eq_add_neg] at h_b_lt_1
              have ⟨n, h_n, _⟩ := h_b_lt_1
              match n with
              | 0 => contradiction -- `0 = 0`
              | .succ n =>
              exists n
              constructor
              · show -b = n
                calc -b
                  _ = -1 + (1 + -b)     := by rw [ℤ.results.ring.add_assoc, ℤ.results.ring.neg_add, ℤ.results.ring.zero_add]
                  _ = -1 + n.succ       := by rw [h_n]
                  _ = ℤ.mk (n.succ, 1)  := by rw [← ℤ.ntn_one, ℤ.results.ring.neg_mk, ℤ.results.ring.add_mk, ℕ.results.arithmetic.zero_add, ℕ.results.arithmetic.add_zero]
                  _ = ℤ.mk (n, 0)       := by
                    apply ℤ.sound
                    show n.succ = n + 1
                    rfl
              · intro h_n_eq_0
                rw [‹n = 0›] at h_n
                have : -b = 0 := calc -b
                  _ = 1 + -b + -1 := by
                    rw  [ ℤ.results.ring.add_comm 1
                        , ← ℤ.results.ring.add_assoc
                        , ℤ.results.ring.add_neg
                        , ℤ.results.ring.add_zero]
                  _ = ℤ.mk (ℕ.succ 0, 0) + -1 := by rw [h_n]
                  _ = ℤ.mk (0, 0) := by
                    rw  [ ← ℤ.ntn_one
                        , ℤ.results.ring.neg_mk
                        , ℤ.results.ring.add_mk
                        , ℕ.results.arithmetic.add_zero
                        , ℕ.results.arithmetic.zero_add]
                    apply ℤ.sound
                    show ℕ.succ 0 = 1
                    rfl
                have : b = 0 := calc b
                  _ = - - b := by rw [ℤ.results.ring.neg_neg]
                  _ = - 0   := by rw [‹-b = 0›]
                  _ = 0     := by rw [ℤ.results.ring.neg_zero_eq_zero]
                contradiction -- `b = 0` and `b ≠ 0`
            have := mul_neg_right (pos_of_gt_1 ‹1 < a›) ‹b < 0›
            have : (0 : ℤ) < 0 :=
              have : x < 0 := by rw [h_ab] ; assumption
              ℤ.results.ordered_ring.lt_trans ‹0 < x› ‹x < 0›
            have : ¬ (0 : ℤ) < 0 := ℤ.results.ordered_ring.lt_irrefl 0
            contradiction -- `0 < 0`
      apply And.intro
      case left => assumption
      case right =>
        show b < x
        rw [h_ab]
        rw [ℤ.results.ordered_ring.lt_mk] at h_1_lt_a
        have : 0 < b := pos_of_gt_1 ‹1 < b›
        rw [ℤ.results.ordered_ring.lt_mk] at this
        have ⟨β, h_β, _⟩ := this
        rw [ℤ.results.ring.sub_zero] at h_β
        have ⟨α, h_α, _⟩ := h_1_lt_a
        have : a = α + 1 := calc a
          _ = (a - 1) + 1 := by rw [ℤ.results.ring.sub_eq_add_neg, ← ℤ.results.ring.add_assoc, ℤ.results.ring.neg_add, ℤ.results.ring.add_zero]
          _ = α + 1       := by rw [h_α]
        rw [ℤ.results.ordered_ring.lt_mk]
        exists α * β
        rw  [ ‹a = α + 1›
            , ℤ.results.ring.add_mul
            , ℤ.results.ring.one_mul
            , ← ℤ.results.ring.add_sub_assoc
            , ℤ.results.ring.sub_self
            , ℤ.results.ring.add_zero
            , h_β
            , ℤ.results.ring.mul_mk
            , ℕ.results.arithmetic.mul_zero
            , ℕ.results.arithmetic.add_zero
            , ℕ.results.arithmetic.mul_zero
            , ℕ.results.arithmetic.zero_mul
            , ℕ.results.arithmetic.add_zero]
        constructor
        · rfl
        · intro h
          have := ℕ.results.arithmetic.null_factor h
          cases this <;> contradiction

  theorem composite_of_not_prime
    {x : ℤ}
    (h_1_lt_x : 1 < x)
    : ¬ x.prime
    → ∃ (a b : ℤ),
        1 < a   ∧ a < x
        ∧ 1 < b ∧ b < x
        ∧ x = a * b
    := by
      rw [ℤ.results.ordered_ring.lt_mk] at h_1_lt_x
      have ⟨δ, h_δ, h_δ_ne_0⟩ := h_1_lt_x
      match δ with
      | 0 => contradiction
      | .succ ε =>
      have : x = ℤ.mk (ε + 2, 0) := calc x
        _ = x - 1 + 1 := by rw [ℤ.results.ring.sub_eq_add_neg, ←ℤ.results.ring.add_assoc, ℤ.results.ring.neg_add, ℤ.results.ring.add_zero]
        _ = ℤ.mk (ε.succ, 0) + 1  := by rw [h_δ]
        _ = ℤ.mk (ε.succ + 1, 0)  := by rw [← ℤ.ntn_one, ℤ.results.ring.add_mk, ℕ.results.arithmetic.add_zero]
        _ = ℤ.mk (ε + 2, 0)       := rfl
      have : 2 ≤ ε + 2 := by
        conv => { lhs; rw [← @ℕ.results.arithmetic.zero_add 2] }
        apply ℕ.results.order.le_add_hom
        · exact ℕ.results.order.le_zero_initial
        · exact ℕ.results.order.le_refl
      intro h_x_n_prime
      rw [‹x = ℤ.mk (ε + 2, 0)›] at h_x_n_prime
      have ⟨p, h_p_prime, ⟨q, h_q⟩⟩ := has_prime_factor_of_not_prime ‹2 ≤ ε + 2› ‹¬ (ℤ.mk (ε + 2, 0)).prime›
      rw [← ‹x = ℤ.mk (ε + 2, 0)›] at h_q
      exists p, q
      show 1 < p ∧ p < x ∧ 1 < q ∧ q < x ∧ x = p * q
      have : p ≠ 0 := by
        intro h
        have := h_p_prime.left
        rw [h, gt_iff_lt, ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub] at this
        have ⟨a, (h_a : ℤ.mk (0, 1) = ℤ.mk (a, 0)), h_a_ne_0⟩ := this
        have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
        contradiction -- `a = 0` and `a ≠ 0`
      have : x > 0 := by
        rw [gt_iff_lt, ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.sub_zero]
        exists ε + 2
        constructor
        · assumption
        · intro h ; injection h
      have : 1 < p := h_p_prime.left
      have : p < x := by
        rw [ℤ.results.ordered_ring.lt_iff_le_and_ne]
        constructor
        · exact ℤ.divisibility.le_of_divides ‹x > 0› (by exists q)
        · intro h_p_eq_x
          rw [‹p = x›, ‹x = ℤ.mk (ε + 2, 0)›] at h_p_prime
          contradiction -- `x` is prime and `x` is not prime
      have ⟨(_ : 1 < q), (_ : q < x)⟩ := suffering ‹x = p * q› ‹0 < x› ‹1 < p› ‹p < x›
      exact ⟨‹1 < p›, ‹p < x›, ‹1 < q›, ‹q < x›, ‹x = p * q›⟩



  /- SECTION: Existence -/

  theorem List.foldr_mul_wrong_base {xs : List ℤ} {b : ℤ} : xs.foldr ℤ.mul b = xs.foldr ℤ.mul 1 * b := by
    induction xs
    case nil =>
      unfold List.foldr
      rw [ℤ.results.ring.spec.one_mul]
    case cons x xs ih =>
      unfold List.foldr
      show x * List.foldr ℤ.mul b xs = x * List.foldr ℤ.mul 1 xs * b
      rw [ih, ℤ.results.ring.spec.mul_assoc]

  theorem fund_arith_exists'
    : ∀ (x : ℕ), 1 ≤ x
        → ∃ (ps : List ℤ),
          (∀ p ∈ ps, p.prime)
          ∧ x = ps.foldr ℤ.mul 1
    := by
      have base_case : ∃ ps, (∀ (p : ℤ), p ∈ ps → p.prime) ∧ ℤ.mk (1, 0) = List.foldr ℤ.mul 1 ps := by
        exists []
        constructor
        · intro p h
          contradiction -- `p ∈ []`
        · simp [ℤ.ntn_one]
      apply ℕ.results.induction.strong_induction_from 1
      · exact base_case
      · -- Recursive case
        intro x h_1_le_x sih
        have h_1_le_x := ℤ.results.coe_ℕ.coe_ℕ_hom_le.mp h_1_le_x
        rw [ℤ.results.ordered_ring.le_iff_lt_or_eq] at h_1_le_x
        cases h_1_le_x
        case a.inr h =>
          have h := ℤ.results.coe_ℕ.coe_ℕ_hom_eq.mpr h |> Eq.symm
          rw [h]
          exact base_case
        case a.inl h_1_lt_x =>
        by_cases h : (x : ℤ).prime
        case pos => -- `h : (x : ℤ).prime`
          exists [x]
          constructor
          · simp [*]
          · simp [ℤ.results.mul_ntn, ℤ.results.ring.mul_one]
        case neg => -- `h : ¬ (x : ℤ).prime`
          by_cases h : x = 0
          case pos =>
            -- show a contradiction
            rw [h] at h_1_le_x
            have ⟨δ, h_δ⟩ := h_1_le_x
            have := h_δ |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
            injection this
          case neg => -- Know `x ≠ 0`
          rw [←ne_eq] at h
          by_cases h : x = 1
          case pos =>
            rw [h]
            exact base_case
          case neg => -- Know `x ≠ 1`
          have : 1 < x := by
            rw [←ne_eq] at h
            match x with
            | 0 => contradiction
            | 1 => contradiction
            | .succ (.succ x) =>
              exists x.succ
              constructor
              · rw  [ ←ℕ.results.ntn.succ_zero_eq_1
                    , ℕ.results.arithmetic.succ_add
                    , ℕ.results.ntn.zero_eq_0
                    , ℕ.results.arithmetic.zero_add]
              · intro h ; injection h

          have : (1 : ℤ) < (x : ℤ) := ℤ.results.coe_ℕ.coe_ℕ_hom_lt.mp ‹1 < x›
          have ⟨a, b, h_1_lt_a, h_a_lt_x, h_1_lt_b, h_b_lt_x, h_x_eq_ab⟩ :=
            composite_of_not_prime ‹(1 : ℤ) < x› ‹¬ (x : ℤ).prime›
          have : 1 ≤ a := ‹1 < a› |> Or.inl |> ℤ.results.ordered_ring.le_iff_lt_or_eq.mpr
          have : 1 ≤ b := ‹1 < b› |> Or.inl |> ℤ.results.ordered_ring.le_iff_lt_or_eq.mpr
          have ⟨α, h_α⟩ := a.existsCanonRep
          have ⟨β, h_β⟩ := b.existsCanonRep
          have : a ≠ ℤ.mk (0, α) := by
            intro h
            have ⟨δ, h_δ⟩ := ‹1 ≤ a›
            rw [h, ← ℤ.ntn_one, ℤ.results.ring.sub_mk, ℕ.results.arithmetic.zero_add] at h_δ
            have : 0 = δ + (α + 1) := h_δ |> ℤ.exact
            rw [ℕ.results.arithmetic.add_assoc, Eq.comm] at this
            have := this |> ℕ.results.arithmetic.args_0_of_add_0 |> And.right
            injection this -- contradiction: `1 = 0`
          have : b ≠ ℤ.mk (0, β) := by
            intro h
            have ⟨δ, h_δ⟩ := ‹1 ≤ b›
            rw [h, ← ℤ.ntn_one, ℤ.results.ring.sub_mk, ℕ.results.arithmetic.zero_add] at h_δ
            have : 0 = δ + (β + 1) := h_δ |> ℤ.exact
            rw [ℕ.results.arithmetic.add_assoc, Eq.comm] at this
            have := this |> ℕ.results.arithmetic.args_0_of_add_0 |> And.right
            injection this -- contradiction: `1 = 0`
          simp [‹a ≠ ℤ.mk (0, α)›] at h_α
          simp [‹b ≠ ℤ.mk (0, β)›] at h_β
          have : 1 ≤ α := by
            apply ℤ.results.coe_ℕ.coe_ℕ_hom_le.mpr
            have := ‹1 ≤ a›
            rw [← ℤ.ntn_one, h_α] at this
            exact this
          have : 1 ≤ β := by
            apply ℤ.results.coe_ℕ.coe_ℕ_hom_le.mpr
            have := ‹1 ≤ b›
            rw [← ℤ.ntn_one, h_β] at this
            exact this
          have : α < x := by
            apply ℤ.results.coe_ℕ.coe_ℕ_hom_lt.mpr
            have := ‹a < x›
            rw [h_α] at this
            exact this
          have : β < x := by
            apply ℤ.results.coe_ℕ.coe_ℕ_hom_lt.mpr
            have := ‹b < x›
            rw [h_β] at this
            exact this
          have ⟨ps, h_ps_prime, h_ps_prod⟩ := sih α ‹1 ≤ α› ‹α < x›
          have ⟨qs, h_qs_prime, h_qs_prod⟩ := sih β ‹1 ≤ β› ‹β < x›
          exists ps ++ qs
          apply And.intro
          case left =>
            show ∀ (p : ℤ), p ∈ ps ++ qs → p.prime
            intro p h
            have h := List.mem_append.mp h
            cases h
            case inl h => exact h_ps_prime p h
            case inr h => exact h_qs_prime p h
          case right =>
            show ℤ.mk (x, 0) = List.foldr ℤ.mul 1 (ps ++ qs)
            have := List.foldr_append ℤ.mul 1 ps qs
            rw  [ this, ←h_qs_prod, List.foldr_mul_wrong_base, ←h_ps_prod
                , ‹x = a * b›, ‹a = α›, ‹b = β›]

  theorem fund_arith_exists
    (x : ℕ)
    {h_x_ne_zero : x ≠ 0}
    : ∃ (ps : List ℤ),
      (∀ p ∈ ps, p.prime)
      ∧ x = ps.foldr ℤ.mul 1
    := by
      have : 1 ≤ x := by
        match x with
        | 0 => contradiction -- `0 ≠ 0`
        | .succ x =>
          exists x
          rw  [ ℕ.results.arithmetic.add_comm
              , ← ℕ.results.ntn.succ_zero_eq_1
              , ℕ.results.arithmetic.add_succ
              , ℕ.results.ntn.zero_eq_0
              , ℕ.results.arithmetic.add_zero]
      exact fund_arith_exists' x ‹1 ≤ x›

end Numbers.fund_arith
