import HRS.MS.ToriCoefAAux3

/-!
# MS-TORI-COEFA, helper file 4: the coefficient `μ_L = Z_L^{-1} perL(ζ_L ρ)` and the lower bound `Z_L ≥ 1/2`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefA

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem tca_const_mul_norm (F : Euc d → ℝ) (n : ℕ) (hF : ContDiff ℝ (n : WithTop ℕ∞) F) (c : ℝ)
    (j : ℕ) (hj : j ≤ n) (w : Euc d) :
    ‖iteratedFDeriv ℝ j (fun x => c * F x) w‖ = |c| * ‖iteratedFDeriv ℝ j F w‖ := by
  have hfun : (fun x => c * F x) = c • F := by
    funext x; rfl
  rw [hfun, iteratedFDeriv_const_smul_apply ((hF.of_le (by exact_mod_cast hj)).contDiffAt),
    norm_smul, Real.norm_eq_abs]

/-- The weighted bound for `ζ_L ρ`, with the Leibniz rule. -/
theorem tca_mu_weighted {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (n : ℕ) (ρ : Euc d → ℝ) (hρ : ContDiff ℝ (n : WithTop ℕ∞) ρ)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (W : ℝ) (hW0 : 0 ≤ W)
    (hWk : ∀ k : ℕ, k ≤ n → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k ρ w‖ ≤ (d : ℝ) ^ k * W)
    (j : ℕ) (hjn : j ≤ n) (w : Euc d) :
    jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ ≤
      tca_S d Kz W j := by
  have hζL := tca_zetaL_contDiff hζ L n
  have hle := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hζL hρ w (n := j) (by exact_mod_cast hjn)
  have hjb : 0 ≤ jbracket w ^ ((d : ℝ) + 3) := Real.rpow_nonneg (tca_jbracket_pos w).le _
  calc jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖
      ≤ jbracket w ^ ((d : ℝ) + 3) * ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) w‖ *
            ‖iteratedFDeriv ℝ (j - i) ρ w‖ :=
        mul_le_mul_of_nonneg_left hle hjb
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) w‖ *
          (jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ (j - i) ρ w‖) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ ≤ tca_S d Kz W j := by
        unfold tca_S
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_range] at hi
        have hX := tca_zetaL_le hζ L hL Kz hKz hKz0 i w
        have hY := hWk (j - i) (by omega) w
        have hC : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
        calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) w‖ *
              (jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ (j - i) ρ w‖)
            ≤ (j.choose i : ℝ) * Kz i * ((d : ℝ) ^ (j - i) * W) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hX hC) hY (mul_nonneg hjb (norm_nonneg _))
                (mul_nonneg hC (hKz0 i))
          _ = (j.choose i : ℝ) * (Kz i * ((d : ℝ) ^ (j - i) * W)) := by ring

theorem tca_mu_global {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (n : ℕ) (ρ : Euc d → ℝ) (hρ : ContDiff ℝ (n : WithTop ℕ∞) ρ)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (W : ℝ) (hW0 : 0 ≤ W)
    (hWk : ∀ k : ℕ, k ≤ n → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k ρ w‖ ≤ (d : ℝ) ^ k * W)
    (j : ℕ) (hjn : j ≤ n) (w : Euc d) :
    ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ ≤ tca_S d Kz W j := by
  have h := tca_mu_weighted hζ L hL n ρ hρ Kz hKz hKz0 W hW0 hWk j hjn w
  have hjb1 : 1 ≤ jbracket w ^ ((d : ℝ) + 3) :=
    Real.one_le_rpow (tca_one_le_jbracket w) (by positivity)
  calc ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖
      ≤ jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hjb1
    _ ≤ tca_S d Kz W j := h

/-- The periodized coefficient `μ_L = perL (c · ζ_L ρ)` (`c = Z_L^{-1} ∈ (0, 2]`): smoothness, the global
`C_b^{n}` bound and the weighted decay bound on the central cube. -/
theorem tca_mu_package {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (n : ℕ) (ρ : Euc d → ℝ) (hρ : ContDiff ℝ (n : WithTop ℕ∞) ρ)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (W : ℝ) (hW0 : 0 ≤ W)
    (hWk : ∀ k : ℕ, k ≤ n → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k ρ w‖ ≤ (d : ℝ) ^ k * W)
    (c : ℝ) (hc0 : 0 < c) (hc2 : c ≤ 2) :
    ContDiff ℝ (n : WithTop ℕ∞) (perL L (fun x => c * (ζ (L⁻¹ • x) * ρ x))) ∧
    (∀ j : ℕ, j ≤ n → ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j (perL L (fun x => c * (ζ (L⁻¹ • x) * ρ x))) x‖ ≤ 2 * tca_S d Kz W j) ∧
    (∀ j : ℕ, j ≤ n → ∀ x : Euc d, ‖x‖ ≤ L / 2 →
      jbracket x ^ ((d : ℝ) + 3) *
        ‖iteratedFDeriv ℝ j (perL L (fun x => c * (ζ (L⁻¹ • x) * ρ x))) x‖ ≤ 2 * tca_S d Kz W j) := by
  have hL0 : 0 < L := by linarith
  have hF : ContDiff ℝ (n : WithTop ℕ∞) (fun x => ζ (L⁻¹ • x) * ρ x) :=
    (tca_zetaL_contDiff hζ L n).mul hρ
  have hf : ContDiff ℝ (n : WithTop ℕ∞) (fun x => c * (ζ (L⁻¹ • x) * ρ x)) :=
    contDiff_const.mul hF
  have hvan : ∀ y : Euc d, L / 3 ≤ ‖y‖ → c * (ζ (L⁻¹ • y) * ρ y) = 0 := by
    intro y hy
    rw [tca_zeta_far_val hζ L hL0 y hy, zero_mul, mul_zero]
  have hS0 := tca_S_nonneg d Kz hKz0 W hW0
  have hglob : ∀ j : ℕ, j ≤ n → ∀ w : Euc d,
      ‖iteratedFDeriv ℝ j (fun x => c * (ζ (L⁻¹ • x) * ρ x)) w‖ ≤ 2 * tca_S d Kz W j := by
    intro j hj w
    have e : ‖iteratedFDeriv ℝ j (fun x => c * (ζ (L⁻¹ • x) * ρ x)) w‖ =
        |c| * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ :=
      tca_const_mul_norm (fun x => ζ (L⁻¹ • x) * ρ x) n hF c j hj w
    rw [e]
    have h1 := tca_mu_global hζ L hL n ρ hρ Kz hKz hKz0 W hW0 hWk j hj w
    have hc : |c| ≤ 2 := by rw [abs_of_pos hc0]; exact hc2
    have h3 : |c| * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ ≤
        2 * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) w‖ :=
      mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    linarith
  refine ⟨tca_perL_contDiff n L hL0 _ hf hvan, fun j hj x => ?_, fun j hj x hx => ?_⟩
  · exact tca_perL_norm_le L hL0 _ hvan j _ (hglob j hj) x
  · rw [tca_perL_central L hL0 _ hvan x hx j]
    have e : ‖iteratedFDeriv ℝ j (fun x => c * (ζ (L⁻¹ • x) * ρ x)) x‖ =
        |c| * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) x‖ :=
      tca_const_mul_norm (fun x => ζ (L⁻¹ • x) * ρ x) n hF c j hj x
    rw [e]
    have hw := tca_mu_weighted hζ L hL n ρ hρ Kz hKz hKz0 W hW0 hWk j hj x
    have hc : |c| ≤ 2 := by rw [abs_of_pos hc0]; exact hc2
    calc jbracket x ^ ((d : ℝ) + 3) * (|c| * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) x‖)
        = |c| * (jbracket x ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * ρ x) x‖) := by
          ring
      _ ≤ |c| * tca_S d Kz W j := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ ≤ 2 * tca_S d Kz W j := mul_le_mul_of_nonneg_right hc (hS0 j)

/-- The lower bound `Z_L = ∫ ζ_L ρ ≥ 1/2` for `L ≥ 4N`, from the tail of the weight. -/
theorem tca_Z_ge {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (ρ : Euc d → ℝ)
    (hρ : HRS.Whole.IsProbDensity ρ) (B : ℝ) (hB0 : 0 ≤ B) (hρB : ∀ y, |ρ y| ≤ B * tca_g y)
    (L : ℝ) (hL : 0 < L) (N : ℕ) (hLN : (N : ℝ) ≤ L / 4) (ε : ℝ)
    (hN : ∫ y in {y : Euc d | (N : ℝ) ≤ ‖y‖}, tca_g y ≤ ε) (hBε : B * ε ≤ 1 / 2) :
    1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ y := by
  have hAm : MeasurableSet {y : Euc d | L / 4 ≤ ‖y‖} :=
    measurableSet_le measurable_const continuous_norm.measurable
  have hρint : Integrable ρ := by
    by_contra h
    have h1 := hρ.integral_one
    rw [integral_undef h] at h1
    norm_num at h1
  have hcont : Continuous (fun y : Euc d => ζ (L⁻¹ • y)) :=
    hζ.1.continuous.comp (continuous_const_smul _)
  have hint1 : Integrable (fun y : Euc d => ζ (L⁻¹ • y) * ρ y) := by
    refine Integrable.mono' hρint.norm
      (hcont.aestronglyMeasurable.mul hρ.measurable.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have hz := hζ.2.2.2.1 (L⁻¹ • y)
    have h1 : ‖ζ (L⁻¹ • y)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hz.1]; exact hz.2
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hbound : ∀ y : Euc d, ‖ζ (L⁻¹ • y) * ρ y - ρ y‖ ≤
      {y : Euc d | L / 4 ≤ ‖y‖}.indicator (fun y => B * tca_g y) y := by
    intro y
    by_cases hy : L / 4 ≤ ‖y‖
    · rw [Set.indicator_of_mem (show y ∈ {y : Euc d | L / 4 ≤ ‖y‖} from hy)]
      have hz01 := hζ.2.2.2.1 (L⁻¹ • y)
      have h1 : ‖ζ (L⁻¹ • y) * ρ y - ρ y‖ = |ζ (L⁻¹ • y) - 1| * |ρ y| := by
        rw [Real.norm_eq_abs, ← abs_mul]
        congr 1
        ring
      have h2 : |ζ (L⁻¹ • y) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hz01.1, hz01.2]
      calc ‖ζ (L⁻¹ • y) * ρ y - ρ y‖ = |ζ (L⁻¹ • y) - 1| * |ρ y| := h1
        _ ≤ 1 * |ρ y| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ = |ρ y| := one_mul _
        _ ≤ B * tca_g y := hρB y
    · rw [Set.indicator_of_notMem (show y ∉ {y : Euc d | L / 4 ≤ ‖y‖} from hy)]
      have hy' : ‖y‖ < L / 4 := lt_of_not_ge hy
      have hz1 : ζ (L⁻¹ • y) = 1 := by
        apply hζ.2.2.2.2
        rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hL), inv_mul_eq_div, div_le_iff₀ hL]
        linarith
      rw [hz1, one_mul, sub_self, norm_zero]
  have hint_ind : Integrable ({y : Euc d | L / 4 ≤ ‖y‖}.indicator (fun y => B * tca_g y)) :=
    (tca_g_integrable.const_mul B).indicator hAm
  have hdiff : (∫ y, ζ (L⁻¹ • y) * ρ y) - 1 = ∫ y, (ζ (L⁻¹ • y) * ρ y - ρ y) := by
    rw [integral_sub hint1 hρint, hρ.integral_one]
  have hb := norm_integral_le_of_norm_le hint_ind (Filter.Eventually.of_forall hbound)
  rw [integral_indicator hAm, integral_const_mul] at hb
  have hmono : ∫ y in {y : Euc d | L / 4 ≤ ‖y‖}, tca_g y ≤ ε := by
    refine le_trans ?_ hN
    refine setIntegral_mono_set tca_g_integrable.integrableOn
      (Filter.Eventually.of_forall fun y => tca_g_nonneg y) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    intro hy
    show (N : ℝ) ≤ ‖y‖
    exact le_trans hLN hy
  have hmain : ‖∫ y, (ζ (L⁻¹ • y) * ρ y - ρ y)‖ ≤ 1 / 2 :=
    hb.trans (le_trans (mul_le_mul_of_nonneg_left hmono hB0) hBε)
  rw [← hdiff, Real.norm_eq_abs] at hmain
  have := (abs_le.1 hmain).1
  linarith

end HRS.MS.ToriCoefA
