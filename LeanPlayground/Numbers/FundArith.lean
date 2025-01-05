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

  -- Work classically, so that every `Prop` is `Decidable`.
  -- This is because I designed `ℤ.le : ℤ → ℤ → Prop`, *not* `: ℤ → ℤ → Bool`, and don't have `ℤ.beq` or anything like that;
  --  i.e. because I designed `ℤ` for *proving*, not for *programming*. As a consequence, writing a "remove an element from a `List ℤ`"
  --  function is nigh-impossible without implementing `instance BEq ℤ` and proving that the instance agrees with the existing `Eq`uality
  --  on `ℤ` (defined by `ℤ.sound`) -- and I really don't want to do all that work.
  -- Next time, perhaps I'll give more thought to considerations like this.
  attribute [instance] Classical.propDecidable



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
        -- constructor
        -- · intro p h
        --   contradiction -- `p ∈ []`
        -- · simp [ℤ.ntn_one]
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



  /- SECTION: Lemmas about primes and products for the Uniqueness proof -/

  theorem eq_of_prime_div_prime {p q : ℤ} : p.prime → q.prime → p ∣ q → p = q := by
    intro h_p_prime h_q_prime h_p_div_q
    have ⟨u, h_u_inv, h_u⟩ := h_q_prime.right h_p_div_q
    have := h_u_inv |> ℤ.arith.solve_invertible
    cases this
    case inl this =>
      cases h_u
      case inl h_u =>
        rw [this, ℤ.results.ring.mul_one] at h_u
        assumption
      case inr h_u =>
        rw [this] at h_u
        have := h_p_prime.left
        rw [h_u] at this
        have : ¬ (1 < (1 : ℤ)) := ℤ.results.ordered_ring.lt_irrefl 1
        contradiction -- `1 < 1`
    case inr this =>
      cases h_u
      case inl h_u =>
        rw [this, ℤ.results.ring.mul_neg_one, Eq.comm, ℤ.results.ring.neg_eq_comm, Eq.comm] at h_u
        have := h_q_prime.left
        rw  [ h_u
            , ← @ℤ.results.ring.neg_neg 1
            , gt_iff_lt
            , ℤ.results.ordered_ring.lt_neg_swap
            ] at this
        -- `this : p < -1`
        have : 1 < p := ‹p.prime›.left
        have : 1 < -(1 : ℤ) := ℤ.results.ordered_ring.lt_trans ‹1 < p› ‹p < -1›
        rw [ℤ.results.ordered_ring.lt_mk] at this
        have ⟨a, h_a, _⟩ := this
        rw [ℤ.results.ring.sub_eq_add_neg, ← ℤ.ntn_one, ℤ.results.ring.neg_mk, ℤ.results.ring.add_mk] at h_a
        have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
        contradiction -- `a = 0` and `a ≠ 0`
      case inr h_u =>
        have := ‹p.prime›.left
        rw [‹p = u›, ‹u = -1›, gt_iff_lt] at this
        rw [ℤ.results.ordered_ring.lt_mk] at this
        have ⟨a, h_a, _⟩ := this
        rw [ℤ.results.ring.sub_eq_add_neg, ← ℤ.ntn_one, ℤ.results.ring.neg_mk, ℤ.results.ring.add_mk] at h_a
        have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
        contradiction -- `a = 0` and `a ≠ 0`

  theorem prime_ndiv_one {p : ℤ} : p.prime → ¬ (p ∣ 1) := by
    intro h_p_prime ⟨q, h_q⟩
    have := ℤ.results.ring.solve_mul_eq_one h_q.symm
    cases this
    case inl this =>
      have := this.left
      have := ‹p.prime›.left
      rw [‹p = 1›] at this
      have : ¬ (1 < (1 : ℤ)) := ℤ.results.ordered_ring.lt_irrefl 1
      contradiction -- `1 < 1`
    case inr this =>
      have := this.left
      have := ‹p.prime›.left
      rw [‹p = -1›, gt_iff_lt] at this
      -- seen a contradiction from `1 < -1` before... I should've factored this out into a separate lemma
      rw [ℤ.results.ordered_ring.lt_mk] at this
      have ⟨a, h_a, _⟩ := this
      rw [ℤ.results.ring.sub_eq_add_neg, ← ℤ.ntn_one, ℤ.results.ring.neg_mk, ℤ.results.ring.add_mk] at h_a
      have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
      contradiction -- `a = 0` and `a ≠ 0`

  theorem nat_of_prime {p : ℤ} : p.prime → ∃ p' : ℕ, p = p' := by
    have ⟨p', h_p'⟩ := p.existsCanonRep
    cases h_p'
    case inl h_p' =>
      intro _
      exists p'
    case inr h_p' =>
      intro h_p_prime
      suffices False by contradiction
      have := ‹p.prime›.left
      rw [gt_iff_lt, ℤ.results.ordered_ring.lt_mk] at this
      have ⟨a, h_a, h_a_ne_0⟩ := this
      rw  [ h_p'
          , ← ℤ.ntn_one
          , ℤ.results.ring.sub_mk
          , ℕ.results.arithmetic.add_zero
          ] at h_a
      have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
      contradiction -- `a = 0` and `a ≠ 0`

  theorem prime_div_element_of_prime_div_product
    {p : ℤ} {xs : List ℤ}
    : p.prime
    → p ∣ xs.foldr ℤ.mul 1
    → ∃ x ∈ xs, p ∣ x
    := by
      intro h_p_prime
      induction xs
      case nil =>
        intro h
        unfold List.foldr at h
        have : ¬ (p ∣ 1) := prime_ndiv_one ‹p.prime›
        contradiction -- `p ∣ 1` and `¬ (p ∣ 1)`
      case cons y xs ih =>
        intro h
        unfold List.foldr at h
        have h : p ∣ y * xs.foldr ℤ.mul 1 := h
        have ⟨p', h_p_eq_p'⟩ := nat_of_prime ‹p.prime›
        have := @Numbers.Modular.results.field.null_factor_divisibility
          p' (‹p = p'› ▸ ‹p.prime›) y (xs.foldr ℤ.mul 1)
          |> Iff.mp
          <| (‹p = p'› ▸ h)
        cases this
        case inl this => -- `this : p' ∣ y`
          exists y
          constructor
          · rw [List.mem_cons]
            apply Or.inl
            rfl
          · rw [‹p = p'›]
            assumption
        case inr this => -- `this : p' ∣ xs.foldr ℤ.mul 1`
          rw [‹p = p'›.symm] at this
          have ⟨x, _, _⟩ := ih this
          exists x
          constructor
          · rw [List.mem_cons]
            apply Or.inr
            assumption
          · assumption

  theorem prime_in_list_of_prime_div_prime_list_product
    {p : ℤ} {ps : List ℤ}
    : p.prime
    → (∀ q ∈ ps, q.prime)
    → p ∣ ps.foldr ℤ.mul 1
    → p ∈ ps
    := by
      intro h_p_prime h_ps_prime h_p_div_product
      have ⟨x, h_x_in_ps, h_p_div_x⟩ := prime_div_element_of_prime_div_product ‹p.prime› h_p_div_product
      have : x.prime := h_ps_prime x ‹x ∈ ps›
      have := eq_of_prime_div_prime ‹p.prime› ‹x.prime› ‹p ∣ x›
      rw [this]
      assumption

end Numbers.fund_arith



namespace List
  open Numbers

  /- SECTION: List preliminaries for the Uniqueness statement and proof -/
  /-- Count the number of occurances of an integer `q` in a list of integers. -/
  noncomputable
  def countℤ (q : ℤ) : List ℤ → Nat
    | [] => 0
    | (x :: xs) => (if q = x then 1 else 0) + xs.countℤ q

  /--
    An argument-swapped version of `List.countℤ`, with the emphasis on returning a function `ℤ → Nat`.
    Functions `ℤ → Nat` may be thought of a *multisets* of integers†, so `xs.counts` should be though of
    as the *multiset induced by `xs`*. As such, `xs.counts = ys.counts` should be thought of as the
    statement that `xs` and `ys` represent the same multiset (although, of course, `xs` and `ys` may list
    the multiset's elements in a different order to each other).

    It is "obviously" true that `xs` and `ys` are "equal up to permutation" iff `xs.counts = ys.counts`.
    However, it seems hellish to try to formalise "equal up to permutation", so I've taken the easy way
    out and relied on `counts` in stating the uniqueness part of the fundamental theorem of arithmetic.

    † Under the following isomorphism:
      A multiset `A` corresponds to the "characteristic function" `x ↦ (number of occurances of x in A)`;
      a function `f` corresponds to the multiset `A` such that for all `x`, `x` occurs exactly `f x` times in `A`.
  -/
  noncomputable
  def counts (xs : List ℤ) : ℤ → Nat := xs.countℤ

  /-- Remove an element from a list, if it exists. -/
  noncomputable
  def remove (z : ℤ) : List ℤ → List ℤ
    | []        => []
    | (x :: xs) => if z = x then xs else x :: xs.remove z

  theorem count_elem {z : ℤ} {xs : List ℤ} : z ∈ xs → 1 ≤ xs.countℤ z := by
    intro h
    match xs with
    | [] => contradiction -- `z ∈ []`
    | (x :: xs) =>
      unfold countℤ
      simp at h
      cases h
      case inl h => simp [h]
      case inr h =>
        split
        case isTrue => simp
        case isFalse =>
          rw [Nat.zero_add]
          exact count_elem h

  theorem remove_count
    (z q : ℤ) (xs : List ℤ)
    : (xs.remove z).countℤ q = xs.countℤ q - (if z ∈ xs ∧ q = z then 1 else 0)
    := by
      match xs with
      | [] => simp [remove, countℤ]
      | (x :: xs) =>
        simp [remove, countℤ]
        by_cases h : z = x
        case pos => -- `h : z = x`
          simp [h]
          by_cases h' : q = x
          case pos => -- `h' : q = x`
            simp [h']
            have : 1 ≤ 1 := Nat.le_refl 1
            conv => {
              rhs
              rw [Nat.add_comm, Nat.add_sub_assoc ‹1 ≤ 1›, Nat.sub_self, Nat.add_zero]
            }
          case neg => -- `h' : q ≠ x`
            rw [← ne_eq] at h'
            simp [h']
        case neg => -- `h : z ≠ x`
          rw [← ne_eq] at h
          simp [h, countℤ, xs.remove_count z q]
          rw [Nat.add_sub_assoc]
          split
          case h.isTrue h =>
            have ⟨_, _⟩ := h
            rw [‹q = z›]
            exact count_elem ‹z ∈ xs›
          case h.isFalse h =>
            exact Nat.zero_le _

  theorem cons_remove_counts
    (z : ℤ) (xs : List ℤ)
    : z ∈ xs
    → (z :: xs.remove z).counts = xs.counts
    := by
      intro h
      apply funext ; intro q
      unfold counts
      simp [countℤ, remove_count, h]
      have : (if q = z then 1 else 0) ≤ countℤ q xs := by
        by_cases h' : q = z <;> simp [h']
        case pos => exact count_elem ‹z ∈ xs›
        -- `case neg =>` already discharged by `<;> simp [h']`
      have : (if q = z then 1 else 0) ≤ if q = z then 1 else 0 := Nat.le_refl _
      rw [← Nat.add_sub_assoc ‹_›, Nat.add_comm _ (countℤ q xs), Nat.add_sub_assoc ‹_›, Nat.sub_self, Nat.add_zero]

  theorem mem_remove {z x : ℤ} {xs : List ℤ} : z ∈ xs.remove x → z ∈ xs := by
    induction xs
    case nil =>
      unfold remove
      intro h; contradiction
    case cons y ys ih =>
      unfold remove
      split
      case isTrue h =>
        intro h
        rw [List.mem_cons]
        exact Or.inr h
      case isFalse h =>
        intro h
        rw [List.mem_cons] at h
        cases h
        case inl h =>
          rw [List.mem_cons]
          exact Or.inl h
        case inr h =>
          rw [List.mem_cons]
          exact Or.inr <| ih h

  theorem remove_mul {z : ℤ} {xs : List ℤ} : z ∈ xs → xs.foldr ℤ.mul 1 = z * (xs.remove z).foldr ℤ.mul 1 := by
    intro h_z_in_xs
    induction xs
    case nil => contradiction -- `z ∈ []`
    case cons x xs ih =>
      unfold remove
      split
      case isTrue h =>
        simp [h]
        rfl -- `.mul = *`
      case isFalse h =>
        have : z ∈ xs := by
          simp [mem_cons, h] at h_z_in_xs
          assumption
        have := ih ‹z ∈ xs›
        simp [this]
        show x * (z * (xs.remove z).foldr ℤ.mul 1) = z * (x * (xs.remove z).foldr ℤ.mul 1)
        simp [ℤ.results.ring.spec.mul_assoc, ℤ.results.ring.spec.mul_comm x]

end List



namespace Numbers.fund_arith
  /- SECTION: Uniqueness -/

  theorem one_not_lt_neg_one : ¬ (1 : ℤ) < -1 := by
    rw [ℤ.results.ordered_ring.lt_mk]
    intro ⟨a, h_a, _⟩
    rw [← ℤ.ntn_one, ℤ.results.ring.neg_mk, ℤ.results.ring.sub_mk, ℕ.results.arithmetic.zero_add] at h_a
    have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
    contradiction -- `a = 0` and `a ≠ 0`

  theorem one_not_lt_zero : ¬ (1 : ℤ) < 0 := by
    intro h
    rw [ℤ.results.ordered_ring.lt_mk, ℤ.results.ring.zero_sub, ← ℤ.ntn_one, ℤ.results.ring.neg_mk] at h
    have ⟨a, h_a, h_a_ne_0⟩ := h
    have := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
    contradiction -- `a ≠ 0` and `a = 0`

  theorem two_ne_zero : (2 : ℕ) ≠ 0 := by
    intro h_2_eq_0
    contradiction

  theorem two_not_le_zero : ¬ (2 : ℕ) ≤ 0 := by
    intro ⟨δ, h_δ⟩
    have := h_δ |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
    contradiction -- `2 = 0`

  theorem prime_not_invertible {p : ℤ} : p.prime → ¬ p.invertible := by
    intro h_p_prime h_p_inv
    have h_1_lt_p := h_p_prime |> And.left
    have := h_p_inv |> ℤ.results.ring.solve_invertible
    cases this
    case inl this =>
      rw [this] at h_1_lt_p
      have : ¬ ((1 : ℤ) < 1) := ℤ.results.ordered_ring.lt_irrefl 1
      contradiction -- `1 < 1`
    case inr this =>
      rw [this] at h_1_lt_p
      have : ¬ ((1 : ℤ) < -1) := one_not_lt_neg_one
      contradiction -- `1 < -1`

  theorem prime_not_zero {p : ℤ} : p.prime → p ≠ 0 := by
    intro h_p_prime _
    rw [‹p = 0›] at h_p_prime
    have := h_p_prime.left
    have := one_not_lt_zero
    contradiction -- `1 < 0`

  theorem prime_ge_two {p : ℤ} : p.prime → 2 ≤ p := by
    intro _
    -- have : p ≠ 1 := by
    --   intro _
    --   have := ‹p.prime›.left
    --   rw [‹p = 1›] at this
    --   have : ¬ (1 < (1 : ℤ)) := ℤ.results.ordered_ring.lt_irrefl 1
    --   contradiction -- `1 < 1`
    have := ‹p.prime›.left
    rw [gt_iff_lt, ℤ.results.ordered_ring.lt_mk] at this
    have ⟨a, h_a, _⟩ := this
    match a with
    | 0 => contradiction -- `0 ≠ 0`
    | .succ b =>
      exists b
      have : p - 2 = p - 1 - 1 := by
        repeat rw [ℤ.results.ring.sub_eq_add_neg]
        rw  [ ← ℤ.results.ring.add_assoc
            , ← ℤ.results.ring.neg_add']
        rfl
      rw [this, h_a, ← ℤ.ntn_one, ℤ.results.ring.sub_mk, ℕ.results.arithmetic.add_zero, ℕ.results.arithmetic.zero_add]
      apply ℤ.sound
      show b.succ = b + 1
      rfl

  theorem exists_nice_prime_factor
    {x : ℕ}
    : 2 ≤ x
    → ∃ (p q : ℕ),
        (p : ℤ).prime
        ∧ 1 ≤ q ∧ q < x
        ∧ x = p * q
    := by
      intro h_2_le_x
      by_cases h : (x : ℤ).prime
      case pos => -- `h : x.prime`
        exists x, 1
        have : (1 : ℕ) ≤ 1 := ℕ.results.order.le_refl
        have : 1 < x := by
          have ⟨a, h_a⟩ := ‹2 ≤ x›
          exists a.succ
          constructor
          · rw [ℕ.results.arithmetic.add_succ, ← ℕ.results.arithmetic.succ_add]
            exact h_a
          · intro h; injection h
        have : x = x * 1 := by rw [ℕ.results.arithmetic.mul_one]
        exact ⟨‹_›, ‹_›, ‹_›, ‹_›⟩
      case neg => -- `h : ¬ x.prime`
        have ⟨p, h_p_prime, ⟨q, h_x_eq_pq⟩⟩ := has_prime_factor_of_not_prime ‹2 ≤ x› h
        have ⟨p', h_p'⟩ := p.existsCanonRep
        have ⟨q', h_q'⟩ := q.existsCanonRep
        cases h_p'
        case inr h_p' =>
          have := ‹p.prime›.left
          rw  [h_p', gt_iff_lt, ℤ.results.ordered_ring.lt_mk
              , ← ℤ.ntn_one
              , ℤ.results.ring.sub_mk
              , ℕ.results.arithmetic.zero_add
              ] at this
          have ⟨a, h_a, _⟩ := this
          have : a = 0 := h_a |> ℤ.exact |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
          contradiction -- `a = 0` and `a ≠ 0`
        case inl h_p' =>
          cases h_q'
          case inr h_q' =>
            suffices False by contradiction
            have ⟨a, h_a⟩ := ‹2 ≤ x›
            rw  [ h_p', h_q', h_a
                , ℤ.results.ring.mul_mk
                , ℕ.results.arithmetic.mul_zero
                , ℕ.results.arithmetic.mul_zero
                , ℕ.results.arithmetic.zero_mul
                , ℕ.results.arithmetic.add_zero
                , ℕ.results.arithmetic.add_zero
                ] at h_x_eq_pq
            have := h_x_eq_pq |> ℤ.exact |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
            have : (2 : ℕ) ≠ 0 := two_ne_zero
            contradiction -- `2 = 0`
          case inl h_q' =>
            exists p', q'
            constructor
            · rw [←h_p']
              assumption
            · constructor
              · match q' with
                | 0 =>
                  rw [h_q', ℤ.ntn_zero, ℤ.results.ring.mul_zero, ← ℤ.ntn_zero] at h_x_eq_pq
                  have : x = 0 := ℤ.results.coe_ℕ.coe_ℕ_hom_eq.mpr h_x_eq_pq
                  rw [‹x = 0›] at h_2_le_x
                  have ⟨δ, h_δ⟩ := h_2_le_x
                  have : (2 : ℕ) = 0 := h_δ |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
                  have : (2 : ℕ) ≠ 0 := two_ne_zero
                  contradiction -- `2 = 0`
                | .succ q' =>
                  exists q'
                  rw [← ℕ.ntn_succ_zero_eq_1, ℕ.results.arithmetic.succ_add, ℕ.ntn_zero_eq_0, ℕ.results.arithmetic.zero_add]
              · constructor
                · show q' < x
                  apply ℤ.results.coe_ℕ.coe_ℕ_hom_lt.mpr
                  rw [ℤ.results.ordered_ring.lt_iff_not_ge]
                  rw [← h_q', h_x_eq_pq, ge_iff_le]
                  intro (h : p * q ≤ q) -- show a contradiction from this information
                  rw  [ h_p', h_q'
                      , ℤ.results.ring.mul_mk
                      , ℕ.results.arithmetic.mul_zero
                      , ℕ.results.arithmetic.mul_zero
                      , ℕ.results.arithmetic.zero_mul
                      , ℕ.results.arithmetic.add_zero
                      , ℕ.results.arithmetic.add_zero
                      , ←ℤ.results.coe_ℕ.coe_ℕ_hom_le
                      ] at h
                  have h_2_le_p : 2 ≤ p := prime_ge_two ‹p.prime›
                  have : (2 : ℤ) = ((2 : ℕ) : ℤ) := rfl
                  rw [h_p', this, ← ℤ.results.coe_ℕ.coe_ℕ_hom_le] at h_2_le_p
                  have := ℕ.results.order.le_mul_hom ‹2 ≤ p'› (@ℕ.results.order.le_refl q')
                  have ⟨δ, h_δ⟩ := ℕ.results.order.le_trans ‹2 * q' ≤ p' * q'› ‹p' * q' ≤ q'›
                  have : 0 = q' + δ := by
                    have : q' + 0 = q' + (q' + δ) := calc q'
                      _ = 2 * q' + δ    := h_δ
                      _ = (q' + q') + δ := by show (ℕ.zero.succ.succ * q') + δ = q' + q' + δ ; simp
                      _ = q' + (q' + δ) := by rw [← ℕ.results.arithmetic.add_assoc]
                    exact this |> ℕ.results.arithmetic.add_left_cancel
                  have : q' = 0 := this |> Eq.symm |> ℕ.results.arithmetic.args_0_of_add_0 |> And.left
                  rw [h_q', ‹q' = 0›, ℤ.ntn_zero, ℤ.results.ring.mul_zero, ← ℤ.ntn_zero, ← ℤ.results.coe_ℕ.coe_ℕ_hom_eq] at h_x_eq_pq
                  rw [‹x = 0›] at h_2_le_x
                  have : ¬ (2 : ℕ) ≤ 0 := two_not_le_zero
                  contradiction -- `2 ≤ 0`
                · rw  [ h_p', h_q', ℤ.results.ring.mul_mk
                      , ℕ.results.arithmetic.mul_zero
                      , ℕ.results.arithmetic.mul_zero
                      , ℕ.results.arithmetic.zero_mul
                      , ℕ.results.arithmetic.add_zero
                      , ℕ.results.arithmetic.add_zero
                      ] at h_x_eq_pq
                  exact ℤ.results.coe_ℕ.coe_ℕ_hom_eq.mpr h_x_eq_pq

  theorem two_le_of_one_le_and_one_ne
    {x : ℕ}
    : x ≠ 1
    → 1 ≤ x
    → 2 ≤ x
    := by
      intros
      have ⟨δ, h_δ⟩ := ‹1 ≤ x›
      match δ with
      | 0 => -- show a contradiction
        rw [ℕ.results.arithmetic.add_zero] at h_δ
        contradiction -- `x = 1` and `x ≠ 1`
      | .succ δ =>
        exists δ
        rw  [ ℕ.results.arithmetic.add_succ
            , ← ℕ.results.arithmetic.succ_add
            ] at h_δ
        exact h_δ

  theorem fund_arith_unique.lemma.base_case'
    : ∀ (ps : List ℤ),
      (∀ p ∈ ps, p.prime)
      → 1 = ps.foldr ℤ.mul 1
      → ps = []
    := by
      intro ps h_ps_prime h_ps_mul_1
      match ps with
      | [] => rfl
      | (p :: ps) =>
        simp at h_ps_mul_1
        have h_ps_mul_1 : 1 = p * ps.foldr ℤ.mul 1 := h_ps_mul_1
        have : p ∣ 1 := by exists ps.foldr ℤ.mul 1
        have : (1 : ℤ).invertible := by exists 1
        have h_p_unit := ℤ.results.number_theory.unit_of_divides_unit ‹(1 : ℤ).invertible› ‹p ∣ 1› |> ℤ.results.ring.solve_invertible
        have : p ∈ p :: ps := by simp
        have := h_ps_prime p ‹p ∈ p :: ps› |> And.left
        cases h_p_unit
        case inl h_p_unit =>
          rw [‹p = 1›] at this
          have : ¬ ((1 : ℤ) < 1) := ℤ.results.ordered_ring.lt_irrefl 1
          contradiction -- `1 < 1`
        case inr h_p_unit =>
          rw [‹p = -1›] at this
          have := one_not_lt_neg_one
          contradiction -- `1 < -1`

  theorem fund_arith_unique.lemma.base_case
    : ∀ (ps qs : List ℤ),
      (∀ p ∈ ps, p.prime)     → (∀ q ∈ qs, q.prime)
      → 1 = ps.foldr ℤ.mul 1  → 1 = qs.foldr ℤ.mul 1
      → ps.counts = qs.counts
    := by
      intro ps qs h_ps_prime h_qs_prime h_ps_mul h_qs_mul
      have : ps = [] := fund_arith_unique.lemma.base_case' ps h_ps_prime h_ps_mul
      have : qs = [] := fund_arith_unique.lemma.base_case' qs h_qs_prime h_qs_mul
      rw [‹ps = []›, ‹qs = []›]

  theorem fund_arith_unique.lemma.prime'
    (x : ℕ)
    : (x : ℤ).prime
    → ∀ (ps : List ℤ),
      (∀ p ∈ ps, p.prime)
      → x = ps.foldr ℤ.mul 1
      → ps = [(x : ℤ)]
    := by
      intro h_x_prime ps h_ps_prime h_ps_mul
      have : (x : ℤ) ∣ ps.foldr ℤ.mul 1 := by rw [h_ps_mul] ; exact ℤ.results.number_theory.divides_refl _
      have := prime_in_list_of_prime_div_prime_list_product ‹(x : ℤ).prime› h_ps_prime ‹_›
      match ps with
      | [] => contradiction -- `x ∈ []`
      | (p :: ps) =>
        have : p ∣ x := by exists ps.foldr ℤ.mul 1
        have : p.prime := h_ps_prime p (by simp)
        have h : p = x := eq_of_prime_div_prime ‹p.prime› ‹(x : ℤ).prime› ‹p ∣ x›
        rw [h]
        suffices ps = [] by rw [this]
        match ps with
        | [] => rfl
        | (q :: ps) =>
          simp [← h] at h_ps_mul
          have h_ps_mul : p = p * (q * ps.foldr ℤ.mul 1) := h_ps_mul
          conv at h_ps_mul => { lhs; rw [← @ℤ.results.ring.mul_one p] }
          have : p ≠ 0 := prime_not_zero (h ▸ h_x_prime)
          have := ℤ.results.ring.mul_left_cancel ‹p ≠ 0› h_ps_mul
          have : q ∣ 1 := by exists List.foldr ℤ.mul 1 ps
          have : (1 : ℤ).invertible := by exists 1
          have := ℤ.results.number_theory.unit_of_divides_unit ‹(1 : ℤ).invertible› ‹q ∣ 1›
          have := h_ps_prime q (by simp) |> prime_not_invertible
          contradiction -- `q.invertible` and `¬ q.invertible`

  theorem fund_arith_unique.lemma.prime
    (x : ℕ)
    : (x : ℤ).prime
    → ∀ (ps qs : List ℤ),
      (∀ p ∈ ps, p.prime)     → (∀ q ∈ qs, q.prime)
      → x = ps.foldr ℤ.mul 1  → x = qs.foldr ℤ.mul 1
      → ps.counts = qs.counts
    := by
      intro _ ps qs _ _ _ _
      have := fund_arith_unique.lemma.prime' x ‹_› ps ‹_› ‹_›
      have := fund_arith_unique.lemma.prime' x ‹_› qs ‹_› ‹_›
      rw [‹ps = [(x : ℤ)]›, ‹qs = [(x : ℤ)]›]

  theorem fund_arith_unique.lemma.from_one
    (x : ℕ)
    : 1 ≤ x
    → ∀ (ps qs : List ℤ),
      (∀ p ∈ ps, p.prime)     → (∀ q ∈ qs, q.prime)
      → x = ps.foldr ℤ.mul 1  → x = qs.foldr ℤ.mul 1
      → ps.counts = qs.counts
    := by
      apply ℕ.results.induction.strong_induction_from 1
      · exact fund_arith_unique.lemma.base_case
      · intro x
        by_cases h' : x = 1
        case pos => -- `h' : x = 1`; i.e. base case (again, ik I should change the type of `ℕ.results.induction.strong_induction_from`, but I'm in too deep now T-T)
          intro _ _
          rw [h']
          exact fund_arith_unique.lemma.base_case
        case neg => -- `h' : x ≠ 1`
          intro h_1_le_x sih ps qs h_ps_prime h_qs_prime h_ps_mul h_qs_mul
          show ps.counts = qs.counts
          by_cases h : (x : ℤ).prime
          case pos => -- `h : x.prime`
            exact fund_arith_unique.lemma.prime x ‹_› ps qs ‹_› ‹_› ‹_› ‹_›
          case neg => -- `h : ¬ x.prime`
            -- TODO: Recurse here
            have : 2 ≤ x := two_le_of_one_le_and_one_ne ‹x ≠ 1› ‹1 ≤ x›
            have ⟨p, q, h_p_prime, h_1_le_q, h_q_lt_x, h_x_eq_pq⟩ := exists_nice_prime_factor ‹2 ≤ x›
            have sih_q := sih q ‹1 ≤ q› ‹q < x›
            have : (p : ℤ) ∣ x := by exists q ; simp [ℤ.results.ring.mul_mk, h_x_eq_pq]
            have : (p : ℤ) ∈ ps := prime_in_list_of_prime_div_prime_list_product ‹(p : ℤ).prime› h_ps_prime (by rw [←h_ps_mul]; assumption)
            have : (p : ℤ) ∈ qs := prime_in_list_of_prime_div_prime_list_product ‹(p : ℤ).prime› h_qs_prime (by rw [←h_qs_mul]; assumption)
            let  ps' := ps.remove (p : ℤ) ; have : ps' = ps.remove (p : ℤ) := rfl
            let  qs' := qs.remove (p : ℤ) ; have : qs' = qs.remove (p : ℤ) := rfl
            have : q = ps'.foldr ℤ.mul 1 := by
              have h := List.remove_mul ‹(p : ℤ) ∈ ps›
              rw  [ ‹ps' = ps.remove (p : ℤ)›.symm
                  , ← h_ps_mul
                  , ‹x = p * q›
                  , ℤ.results.coe_ℕ.coe_ℕ_hom_mul
                  ] at h
              exact ℤ.results.ring.mul_left_cancel (prime_not_zero ‹(p : ℤ).prime›) h
            have : q = qs'.foldr ℤ.mul 1 := by
              have h := List.remove_mul ‹(p : ℤ) ∈ qs›
              rw  [ ‹qs' = qs.remove (p : ℤ)›.symm
                  , ← h_qs_mul
                  , ‹x = p * q›
                  , ℤ.results.coe_ℕ.coe_ℕ_hom_mul
                  ] at h
              exact ℤ.results.ring.mul_left_cancel (prime_not_zero ‹(p : ℤ).prime›) h
            have : ∀ (r : ℤ), r ∈ ps' → r.prime := by
              intro r h_r_in_ps'
              have : r ∈ ps := List.mem_remove ‹r ∈ ps'›
              exact h_ps_prime r ‹r ∈ ps›
            have : ∀ (r : ℤ), r ∈ qs' → r.prime := by
              intro r h_r_in_qs'
              have : r ∈ qs := List.mem_remove ‹r ∈ qs'›
              exact h_qs_prime r ‹r ∈ qs›
            have : ps'.counts = qs'.counts := sih_q ps' qs' ‹_› ‹_› ‹_› ‹_›
            rw  [ ← List.cons_remove_counts (p : ℤ) ps ‹(p : ℤ) ∈ ps›
                , ‹ps' = ps.remove (p : ℤ)›.symm
                , ← List.cons_remove_counts (p : ℤ) qs ‹(p : ℤ) ∈ qs›
                , ‹qs' = qs.remove (p : ℤ)›.symm]
            apply funext ; intro t
            unfold List.counts List.countℤ
            have : ps'.countℤ t = ps'.counts t := rfl
            rw [this]
            have : qs'.countℤ t = qs'.counts t := rfl
            rw [this]
            suffices ps'.counts = qs'.counts by rw [this]
            assumption

  theorem fund_arith_unique
    (x : ℕ)
    {h_x_ne_zero : x ≠ 0}
    : ∀ (ps qs : List ℤ),
      (∀ p ∈ ps, p.prime)     → (∀ q ∈ qs, q.prime)
      → x = ps.foldr ℤ.mul 1  → x = qs.foldr ℤ.mul 1
      → ps.counts = qs.counts
    := by
      have : 1 ≤ x := by
        match x with
        | 0 => contradiction
        | .succ x' =>
          exists x'
          rw [← ℕ.ntn_succ_zero_eq_1, ℕ.results.arithmetic.succ_add, ℕ.ntn_zero_eq_0, ℕ.results.arithmetic.zero_add]
      exact fund_arith_unique.lemma.from_one x ‹1 ≤ x›



  /- SECTION: The fundamental theorem of arithmetic -/

  theorem fund_arith
    (x : ℕ)
    (h : x ≠ 0)
    : (∃ (ps : List ℤ),
        (∀ p ∈ ps, p.prime)
        ∧ x = ps.foldr ℤ.mul 1
      ) ∧ ∀ (ps qs : List ℤ),
        (∀ p ∈ ps, p.prime)     → (∀ q ∈ qs, q.prime)
        → x = ps.foldr ℤ.mul 1  → x = qs.foldr ℤ.mul 1
        → ps.counts = qs.counts
    := by constructor <;> (first | exact @fund_arith_exists x ‹x ≠ 0› | exact @fund_arith_unique x ‹x ≠ 0›)

  #print axioms fund_arith -- *`'Numbers.fund_arith.fund_arith' depends on axioms: [propext, Classical.choice, Quot.sound]`*

end Numbers.fund_arith
