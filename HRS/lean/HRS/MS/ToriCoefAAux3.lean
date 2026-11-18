import HRS.MS.ToriCoefAAux2

/-!
# MS-TORI-COEFA, helper file 3: scaled cutoffs and the bounds on `V_L = perL (ζ_L V)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefA

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem tca_zeta_contDiff {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) ζ :=
  hζ.1.of_le (by exact_mod_cast le_top)

theorem tca_zetaL_contDiff {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun z : Euc d => ζ (L⁻¹ • z)) :=
  (tca_zeta_contDiff hζ n).comp (contDiff_id.const_smul L⁻¹)

theorem tca_zeta_far_val {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 0 < L)
    (y : Euc d) (hy : L / 3 ≤ ‖y‖) : ζ (L⁻¹ • y) = 0 := by
  by_contra h
  have hs : L⁻¹ • y ∈ tsupport ζ := subset_tsupport _ h
  have := hζ.2.2.1 hs
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL),
    inv_mul_eq_div, div_lt_iff₀ hL] at this
  linarith

/-- The scaled cutoff derivatives are bounded by the unscaled ones when `L ≥ 1`. -/
theorem tca_zetaL_le {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (_hKz0 : ∀ i, 0 ≤ Kz i) (i : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ ≤ Kz i := by
  have ha0 : 0 < L⁻¹ := inv_pos.2 (by linarith)
  have ha1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  rw [tca_scaled_iter i ζ (tca_zeta_contDiff hζ i) L y, abs_of_pos ha0]
  have h1 : L⁻¹ ^ i ≤ 1 := pow_le_one₀ ha0.le ha1
  have h2 := hKz i (L⁻¹ • y)
  have h3 : 0 ≤ ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ := norm_nonneg _
  calc L⁻¹ ^ i * ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ ≤ 1 * ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ :=
        mul_le_mul_of_nonneg_right h1 h3
    _ ≤ Kz i := by rw [one_mul]; exact h2

/-- The scaled cutoff derivatives of order `i ≥ 1` carry the factor `L⁻¹`. -/
theorem tca_zetaL_le_small {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (i : ℕ) (hi : 1 ≤ i) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ ≤ L⁻¹ * Kz i := by
  have ha0 : 0 < L⁻¹ := inv_pos.2 (by linarith)
  have ha1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  rw [tca_scaled_iter i ζ (tca_zeta_contDiff hζ i) L y, abs_of_pos ha0]
  have h1 : L⁻¹ ^ i ≤ L⁻¹ := pow_le_of_le_one ha0.le ha1 (by omega)
  have h2 := hKz i (L⁻¹ • y)
  have h3 : 0 ≤ ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ := norm_nonneg _
  calc L⁻¹ ^ i * ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ ≤ L⁻¹ * ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ :=
        mul_le_mul_of_nonneg_right h1 h3
    _ ≤ L⁻¹ * Kz i := mul_le_mul_of_nonneg_left h2 ha0.le

/-- The constant `S_j` of the `μ_L` bounds. -/
def tca_S (d : ℕ) (Kz : ℕ → ℝ) (W : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Kz i * ((d : ℝ) ^ (j - i) * W))

/-- The constant `V_j` of the `V_L` bounds. -/
def tca_Vb (Kz : ℕ → ℝ) (M : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (Kz i * M)

theorem tca_S_nonneg (d : ℕ) (Kz : ℕ → ℝ) (hKz0 : ∀ i, 0 ≤ Kz i) (W : ℝ) (hW : 0 ≤ W) (j : ℕ) :
    0 ≤ tca_S d Kz W j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (hKz0 i) (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) hW))

theorem tca_Vb_nonneg (Kz : ℕ → ℝ) (hKz0 : ∀ i, 0 ≤ Kz i) (M : ℝ) (hM : 0 ≤ M) (j : ℕ) :
    0 ≤ tca_Vb Kz M j :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKz0 i) hM)

/-- The term bound for the `V`-Leibniz sum. -/
theorem tca_V_term {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (n : ℕ) (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV G₀ V₀ : ℝ)
    (hΛ0 : 0 ≤ ΛV) (hG0 : 0 ≤ G₀) (hV0₀ : 0 ≤ V₀)
    (hVk : ∀ k : ℕ, 2 ≤ k → k ≤ n → ∀ x : Euc d, ‖iteratedFDeriv ℝ k V x‖ ≤ ΛV)
    (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV)
    (hV3 : ‖gradient V 0‖ ≤ G₀) (hV0 : |V 0| ≤ V₀)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (M : ℝ) (hM : V₀ + G₀ + ΛV ≤ M)
    (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) (i : ℕ) (hi : i ≤ j) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖ ≤ Kz i * M := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < L⁻¹ := inv_pos.2 hL0
  have ha1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  have haL : L⁻¹ * L = 1 := inv_mul_cancel₀ hL0.ne'
  have hM0 : 0 ≤ M := by linarith
  have hXle : ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ ≤ Kz i :=
    tca_zetaL_le hζ L hL Kz hKz hKz0 i y
  have hX0 : 0 ≤ ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ := norm_nonneg _
  have hY0 : 0 ≤ ‖iteratedFDeriv ℝ (j - i) V y‖ := norm_nonneg _
  rcases (show j - i ≥ 2 ∨ j - i = 1 ∨ j - i = 0 by omega) with h | h | h
  · -- derivative of order `j - i ≥ 2` of `V` is bounded by `ΛV`
    have hY : ‖iteratedFDeriv ℝ (j - i) V y‖ ≤ ΛV := hVk (j - i) h (by omega) y
    calc ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖
        ≤ Kz i * ΛV := mul_le_mul hXle hY hY0 (hKz0 i)
      _ ≤ Kz i * M := mul_le_mul_of_nonneg_left (by linarith) (hKz0 i)
  · -- `j - i = 1`, so `i ≥ 1`
    have hi1 : 1 ≤ i := by omega
    by_cases hy : L / 3 ≤ ‖y‖
    · rw [tca_zero_far L hL0 ζ hζ i (tca_zeta_contDiff hζ i) y hy, zero_mul]
      exact mul_nonneg (hKz0 i) hM0
    · push_neg at hy
      have hY : ‖iteratedFDeriv ℝ (j - i) V y‖ ≤ G₀ + ΛV * ‖y‖ := by
        rw [h, norm_iteratedFDeriv_one]
        exact tca_fderiv_bound V hV1 ΛV G₀ hΛ0 hV2 hV3 y
      have hXs := tca_zetaL_le_small hζ L hL Kz hKz i hi1 y
      have hr : L⁻¹ * ‖y‖ ≤ 1 / 3 := by
        have h1 := mul_le_mul_of_nonneg_left hy.le ha0.le
        have h2 : L⁻¹ * (L / 3) = 1 / 3 := by
          rw [← mul_div_assoc, haL]
        linarith
      have hXY : ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖ ≤
          (L⁻¹ * Kz i) * (G₀ + ΛV * ‖y‖) :=
        mul_le_mul hXs hY hY0 (mul_nonneg ha0.le (hKz0 i))
      have hG : L⁻¹ * G₀ ≤ G₀ := by
        have := mul_le_mul_of_nonneg_right ha1 hG0
        linarith
      have hΛ : ΛV * (L⁻¹ * ‖y‖) ≤ ΛV := by
        have := mul_le_mul_of_nonneg_left hr hΛ0
        linarith
      calc ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖
          ≤ (L⁻¹ * Kz i) * (G₀ + ΛV * ‖y‖) := hXY
        _ = Kz i * (L⁻¹ * G₀ + ΛV * (L⁻¹ * ‖y‖)) := by ring
        _ ≤ Kz i * M := mul_le_mul_of_nonneg_left (by linarith) (hKz0 i)
  · -- `j - i = 0`, so `i = j ≥ 2`
    have hi2 : 2 ≤ i := by omega
    by_cases hy : L / 3 ≤ ‖y‖
    · rw [tca_zero_far L hL0 ζ hζ i (tca_zeta_contDiff hζ i) y hy, zero_mul]
      exact mul_nonneg (hKz0 i) hM0
    · push_neg at hy
      have hs0 : 0 ≤ L⁻¹ * ‖y‖ := mul_nonneg ha0.le (norm_nonneg _)
      have hs : L⁻¹ * ‖y‖ ≤ 1 / 3 := by
        have h1 := mul_le_mul_of_nonneg_left hy.le ha0.le
        have h2 : L⁻¹ * (L / 3) = 1 / 3 := by
          rw [← mul_div_assoc, haL]
        linarith
      have hXs : ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ ≤ L⁻¹ ^ 2 * Kz i := by
        rw [tca_scaled_iter i ζ (tca_zeta_contDiff hζ i) L y, abs_of_pos ha0]
        have h1 : L⁻¹ ^ i ≤ L⁻¹ ^ 2 := pow_le_pow_of_le_one ha0.le ha1 hi2
        have h2 := hKz i (L⁻¹ • y)
        calc L⁻¹ ^ i * ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖
            ≤ L⁻¹ ^ 2 * ‖iteratedFDeriv ℝ i ζ (L⁻¹ • y)‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
          _ ≤ L⁻¹ ^ 2 * Kz i := mul_le_mul_of_nonneg_left h2 (by positivity)
      have hVy : ‖iteratedFDeriv ℝ (j - i) V y‖ ≤ V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖ := by
        rw [h, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact tca_val_bound V hV1 ΛV G₀ V₀ hΛ0 hV2 hV3 hV0 y
      have hsum : L⁻¹ ^ 2 * (V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖) ≤ M := by
        have ea : L⁻¹ ^ 2 * (V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖) =
            L⁻¹ ^ 2 * V₀ + G₀ * L⁻¹ * (L⁻¹ * ‖y‖) + ΛV * (L⁻¹ * ‖y‖) ^ 2 := by
          ring
        have a2 : L⁻¹ ^ 2 ≤ 1 := pow_le_one₀ ha0.le ha1
        have b1 : L⁻¹ ^ 2 * V₀ ≤ V₀ := by nlinarith
        have b2 : G₀ * L⁻¹ * (L⁻¹ * ‖y‖) ≤ G₀ := by
          have h3 : L⁻¹ * (L⁻¹ * ‖y‖) ≤ 1 := by nlinarith
          nlinarith
        have b3 : ΛV * (L⁻¹ * ‖y‖) ^ 2 ≤ ΛV := by
          have h3 : (L⁻¹ * ‖y‖) ^ 2 ≤ 1 := by nlinarith
          nlinarith
        linarith
      have hYY : ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖ ≤
          (L⁻¹ ^ 2 * Kz i) * (V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖) :=
        mul_le_mul hXs hVy hY0 (mul_nonneg (by positivity) (hKz0 i))
      calc ‖iteratedFDeriv ℝ i (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ (j - i) V y‖
          ≤ (L⁻¹ ^ 2 * Kz i) * (V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖) := hYY
        _ = Kz i * (L⁻¹ ^ 2 * (V₀ + (G₀ + ΛV * ‖y‖) * ‖y‖)) := by ring
        _ ≤ Kz i * M := mul_le_mul_of_nonneg_left hsum (hKz0 i)

/-- The `V`-Leibniz bound: `‖∇^j (ζ_L V)(y)‖ ≤ V_j` for every `y`, `2 ≤ j ≤ n`. -/
theorem tca_VL_bound {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (n : ℕ) (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV G₀ V₀ : ℝ)
    (hΛ0 : 0 ≤ ΛV) (hG0 : 0 ≤ G₀) (hV0₀ : 0 ≤ V₀)
    (hVk : ∀ k : ℕ, 2 ≤ k → k ≤ n → ∀ x : Euc d, ‖iteratedFDeriv ℝ k V x‖ ≤ ΛV)
    (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV)
    (hV3 : ‖gradient V 0‖ ≤ G₀) (hV0 : |V 0| ≤ V₀)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (M : ℝ) (hM : V₀ + G₀ + ΛV ≤ M)
    (j : ℕ) (hj2 : 2 ≤ j) (hjn : j ≤ n) (y : Euc d) :
    ‖iteratedFDeriv ℝ j (fun x => ζ (L⁻¹ • x) * V x) y‖ ≤ tca_Vb Kz M j := by
  have hζL : ContDiff ℝ ∞ (fun z : Euc d => ζ (L⁻¹ • z)) :=
    hζ.1.comp (contDiff_id.const_smul L⁻¹)
  have hle := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hζL hV1 y (n := j) (by exact_mod_cast le_top)
  refine hle.trans ?_
  unfold tca_Vb
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_range] at hi
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (tca_V_term hζ L hL n V hV1 ΛV G₀ V₀ hΛ0 hG0 hV0₀ hVk hV2 hV3 hV0 Kz hKz hKz0 M hM j hj2 hjn i
      (by omega) y) (Nat.cast_nonneg _)

end HRS.MS.ToriCoefA
