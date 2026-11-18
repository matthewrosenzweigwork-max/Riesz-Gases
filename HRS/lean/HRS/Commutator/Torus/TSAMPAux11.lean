import HRS.Commutator.Torus.TSAMPAux10
import HRS.Commutator.Whole.ExternalAuxMult4

/-!
# T-SAMP helpers, part 11: the `ℝ^d` multiplier kernels with bounds, periodised
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The Riesz-type kernel `K_γ` of `(3.K-bounds)` on `ℝ^d`: measurable version with bounds. -/
theorem tsamp_Kalpha_data (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d) :
    ∃ Kt : Euc d → ℝ, Measurable Kt ∧ Integrable Kt ∧
      (∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((Kt x : ℝ) : ℂ)) ξ =
        (((1 - Whole.chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ) : ℝ) : ℂ)) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧ (∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |Kt x| ≤ C₀ * ‖x‖ ^ (γ - d)) ∧
        ∃ Cf : ℕ → ℝ, (∀ m, 0 < Cf m) ∧
          ∀ (m : ℕ) (x : Euc d), 1 ≤ ‖x‖ → |Kt x| ≤ Cf m * ‖x‖ ^ (-(m : ℝ)) := by
  obtain ⟨Kt, hKint, hFT, ⟨C₀, hC₀, hnear⟩, hfar⟩ := Whole.cmxMY_mult_kernel_bounds hd γ hγ hγd
  choose Cf hCf using hfar
  obtain ⟨K', hKm, hae, hnear', hfar'⟩ := text_meas_version hKint hC₀.le hnear Cf
    (fun m => (hCf m).1.le) (fun m => (hCf m).2)
  have hK'int : Integrable K' := hKint.congr (hae.mono fun x hx => hx.symm)
  refine ⟨K', hKm, hK'int, fun ξ => ?_, C₀, hC₀, hnear', Cf, fun m => (hCf m).1, hfar'⟩
  rw [← hFT ξ]
  simp only [Real.fourier_eq]
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-- The Bessel remainder kernel on `ℝ^d` with bounds (`|k(x)| ≲ |x|^{2-d}` near, rapid decay far). -/
theorem tsamp_bessel_data (hd : 3 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∃ kt : Euc d → ℝ, Measurable kt ∧ Integrable kt ∧
      (∀ ξ : Euc d,
        (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) *
          ((1 - Whole.chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) : ℝ) : ℂ) =
          (((1 - Whole.chi ξ : ℝ)) : ℂ) + 𝓕 (fun x : Euc d => ((kt x : ℝ) : ℂ)) ξ) ∧
      ∃ C₀ : ℝ, 0 < C₀ ∧ (∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |kt x| ≤ C₀ * ‖x‖ ^ ((2 : ℝ) - d)) ∧
        ∃ Cf : ℕ → ℝ, (∀ m, 0 < Cf m) ∧
          ∀ (m : ℕ) (x : Euc d), 1 ≤ ‖x‖ → |kt x| ≤ Cf m * ‖x‖ ^ (-(m : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) < d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨K, hK, hF, hfar, hnear⟩ := Whole.cmxMY_LP hd1 (γ := 2) (by norm_num) (Whole.cmxMY_thB (α / 2))
    (Whole.cmxMY_thB_contDiff (α / 2)) (Whole.cmxMY_thB_supp (α / 2)) (Whole.cmxMY_thB_bdd (α / 2))
  have hq : ∀ ξ : Euc d, 𝓕 K ξ = ((Whole.cmxMY_qB (α / 2) ξ : ℝ) : ℂ) := by
    intro ξ
    have h1 := hF ξ
    simp_rw [Whole.cmxMY_thB_piece] at h1
    have h2 : HasSum (fun j : ℕ => ((Whole.cmxMY_rho (((2 : ℝ) ^ j)⁻¹ • ξ) * Whole.cmxMY_qB (α / 2) ξ : ℝ) : ℂ))
        ((Whole.cmxMY_qB (α / 2) ξ : ℝ) : ℂ) := by
      by_cases hξ : 1 ≤ ‖ξ‖
      · have := (Whole.cmxMY_rho_sum_eq_one hξ).mul_right (Whole.cmxMY_qB (α / 2) ξ)
        rw [one_mul] at this
        exact Complex.ofRealCLM.hasSum this
      · have hc : Whole.chi ξ = 1 := Whole.cmxFB_chi_one (by linarith)
        have h0 : Whole.cmxMY_qB (α / 2) ξ = 0 := by simp [Whole.cmxMY_qB, hc]
        simp only [h0, mul_zero, Complex.ofReal_zero]
        exact hasSum_zero
    exact h1.unique h2
  have heven : ∀ ξ : Euc d, Whole.cmxMY_qB (α / 2) (-ξ) = Whole.cmxMY_qB (α / 2) ξ :=
    Whole.cmxMY_qB_even _
  have hFre : ∀ ξ, 𝓕 (fun x => (((K x).re : ℝ) : ℂ)) ξ = ((Whole.cmxMY_qB (α / 2) ξ : ℝ) : ℂ) :=
    Whole.cmxMY_real_part K hK _ heven hq
  obtain ⟨C₁, hC₁⟩ := hnear hd2
  choose Cm hCm using hfar
  have hint : Integrable (fun x => (K x).re) := hK.re
  obtain ⟨K', hKm, hae, hnear', hfar'⟩ := text_meas_version (γ := 2) (Kt := fun x => (K x).re) hint
    (C₀ := |C₁| + 1) (by positivity)
    (fun x hx hx1 => by
      have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hp : 0 < ‖x‖ ^ ((2 : ℝ) - d) := Real.rpow_pos_of_pos hx0 _
      calc |(K x).re| ≤ ‖K x‖ := Complex.abs_re_le_norm _
        _ ≤ C₁ * ‖x‖ ^ ((2 : ℝ) - d) := hC₁ x hx hx1
        _ ≤ (|C₁| + 1) * ‖x‖ ^ ((2 : ℝ) - d) := by
            gcongr
            linarith [le_abs_self C₁])
    (fun m => |Cm m| + 1) (fun m => by positivity)
    (fun m x hx => by
      have hx0 : 0 < ‖x‖ := by linarith
      have hp : 0 < ‖x‖ ^ (-(m : ℝ)) := Real.rpow_pos_of_pos hx0 _
      calc |(K x).re| ≤ ‖K x‖ := Complex.abs_re_le_norm _
        _ ≤ Cm m * ‖x‖ ^ (-(m : ℝ)) := (hCm m) x hx
        _ ≤ (|Cm m| + 1) * ‖x‖ ^ (-(m : ℝ)) := by
            gcongr
            linarith [le_abs_self (Cm m)])
  have hK'int : Integrable K' := hint.congr (hae.mono fun x hx => hx.symm)
  have hFT' : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K' x : ℝ) : ℂ)) ξ =
      ((Whole.cmxMY_qB (α / 2) ξ : ℝ) : ℂ) := by
    intro ξ
    rw [← hFre ξ]
    simp only [Real.fourier_eq]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]
  refine ⟨K', hKm, hK'int, fun ξ => ?_, |C₁| + 1, by positivity, hnear', fun m => |Cm m| + 1,
    fun m => by positivity, hfar'⟩
  rw [hFT' ξ, Whole.cmxMY_bessel_symbol]
  push_cast
  ring

end HRS.Commutator.TorusNote
