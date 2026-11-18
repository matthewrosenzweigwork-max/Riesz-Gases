import HRS.MS.R26T8AL1

/-!
# S8.2 observed-time layer, generic lemma L2: Sobolev bound of a partial derivative of a `SobSmooth` function

For `u` with `r26t8a_SobSmooth u`, every real order `r` and every coordinate `i`:
`sobolevNormE r (∂_i u) ≤ sobolevNormE (r+1) u`  (constant one).
Route: L1 gives `fourierL2 (∂_i u) = 2π i ξ_i · fourierL2 u` a.e.; then `|2π ξ_i|² ≤ 1 + 4π²|ξ|²` and
monotonicity of the Sobolev integrand in the weight `wt^r ≤ wt^(r+1)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_l2_mul_norm (i : Fin d) (ξ : Euc d) (z : ℂ) :
    ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) * z‖ ^ 2 ≤ wt ξ * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  have hn : ‖(2 * Real.pi * Complex.I * (ξ i : ℂ))‖ ^ 2 ≤ wt ξ := by
    have e : ‖(2 * Real.pi * Complex.I * (ξ i : ℂ))‖ = 2 * Real.pi * |ξ i| := by
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [e, mul_pow]
    have hi : |ξ i| ^ 2 ≤ ‖ξ‖ ^ 2 := by
      have := PiLp.norm_apply_le ξ i
      rw [Real.norm_eq_abs] at this
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have h4 := mul_le_mul_of_nonneg_left hi (sq_nonneg (2 * Real.pi))
    unfold wt
    nlinarith [h4, Real.pi_pos]
  exact mul_le_mul_of_nonneg_right hn (sq_nonneg _)

theorem r26t8a_l2 {u : Euc d → ℝ} (hu : r26t8a_SobSmooth u) (i : Fin d) (r : ℝ) :
    sobolevNormE r (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) ≤
      sobolevNormE (r + 1) u := by
  by_cases h1 : HRS.PDE.ToolboxRd.MemSobolev (r + 1) u
  swap
  · unfold sobolevNormE
    rw [if_neg h1]
    exact le_top
  obtain ⟨hD, hF⟩ := r26t8a_l1 hu i
  have hae : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ‖fourierL2 (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2 ≤
        wt ξ * ‖fourierL2 u ξ‖ ^ 2 := by
    filter_upwards [hF] with ξ hξ
    rw [hξ]
    exact r26t8a_l2_mul_norm i ξ _
  have hmem : HRS.PDE.ToolboxRd.MemSobolev r (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) := by
    refine ⟨hD, ?_⟩
    have hI : Integrable (fun ξ => wt ξ ^ (r + 1) * ‖fourierL2 u ξ‖ ^ 2) volume := h1.2
    refine Integrable.mono' hI ?_ ?_
    · exact aesm_wt_mul (aestronglyMeasurable_fourierL2 hD) r
    · filter_upwards [hae] with ξ hξ
      have hw : wt ξ ^ (r + 1) = wt ξ ^ r * wt ξ := by
        rw [Real.rpow_add (wt_pos ξ), Real.rpow_one]
      show ‖wt ξ ^ r * ‖fourierL2 (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2‖ ≤
        wt ξ ^ (r + 1) * ‖fourierL2 u ξ‖ ^ 2
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le r) (sq_nonneg _))]
      calc wt ξ ^ r * ‖fourierL2 (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2
          ≤ wt ξ ^ r * (wt ξ * ‖fourierL2 u ξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hξ (Real.rpow_nonneg (wt_pos ξ).le r)
        _ = wt ξ ^ (r + 1) * ‖fourierL2 u ξ‖ ^ 2 := by rw [hw]; ring
  unfold sobolevNormE
  rw [if_pos hmem, if_pos h1]
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
  unfold sobolevNormSq
  refine integral_mono_ae ?_ ?_ ?_
  · exact hmem.2
  · exact h1.2
  · filter_upwards [hae] with ξ hξ
    have hw : wt ξ ^ (r + 1) = wt ξ ^ r * wt ξ := by
      rw [Real.rpow_add (wt_pos ξ), Real.rpow_one]
    show wt ξ ^ r * ‖fourierL2 (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2 ≤
      wt ξ ^ (r + 1) * ‖fourierL2 u ξ‖ ^ 2
    calc wt ξ ^ r * ‖fourierL2 (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) ξ‖ ^ 2
        ≤ wt ξ ^ r * (wt ξ * ‖fourierL2 u ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hξ (Real.rpow_nonneg (wt_pos ξ).le r)
      _ = wt ξ ^ (r + 1) * ‖fourierL2 u ξ‖ ^ 2 := by rw [hw]; ring

end HRS.MS.R26T8A

end
