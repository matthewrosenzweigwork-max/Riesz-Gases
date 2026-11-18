import HRS.MS.R26T8AP10a17
import HRS.MS.R26T8AP10a16
import HRS.MS.R26T8AP10a13
import HRS.MS.R26T8AP10a7
import HRS.MS.R26T8AP10a6

/-!
# S8.2 T8A P11g (part 1): cut-off integration by parts against a bounded `C^1` function
For `h` with `R26P10Hyp d y τ h` and a bounded `C^1` function `Γ` with bounded gradient:
`∫ Γ div h = - ∑_j ∫ ∂_j Γ h_j` (both integrands integrable).  Copy of P10a6/P10a7 with `keps(x-·)` replaced by `Γ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_g1_ibp_j {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {y : Euc d} {τ : ℝ}
    {h : Euc d → Euc d} (H : R26P10Hyp d y τ h) {Γ : Euc d → ℝ} (hΓ : ContDiff ℝ 1 Γ)
    {B0 B1 : ℝ} (hB0 : ∀ u, |Γ u| ≤ B0) (hB1 : ∀ u, ‖fderiv ℝ Γ u‖ ≤ B1)
    {δ : ℝ} (hδ : 0 < δ) {Cχ : ℝ} (hCχ : ∀ u : Euc d, ‖fderiv ℝ (r26t8a_cut chi y δ) u‖ ≤ Cχ / δ)
    (j : Fin d) :
    Integrable (fun u => Γ u * r26t8a_Dj chi y δ h j u) ∧
    Integrable (fun u => fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u) ∧
    ∫ u, Γ u * r26t8a_Dj chi y δ h j u =
      -∫ u, fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u := by
  have hd := H.hd
  have hτd : τ + 1 < (d : ℝ) := H.τd
  have hτ0 := H.τ0
  have hHc := r26t8a_Hj_continuous hchi hδ H.C1 j
  have hGc : Continuous Γ := hΓ.continuous
  have hdc : Continuous fun u : Euc d => fderiv ℝ Γ u (EuclideanSpace.single j 1) :=
    (hΓ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have hD : ∀ u : Euc d, |fderiv ℝ Γ u (EuclideanSpace.single j 1)| ≤ B1 := by
    intro u
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ Γ u (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ Γ u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ := (fderiv ℝ Γ u).le_opNorm _
      _ ≤ B1 := by rw [r26t8a_norm_single, mul_one]; exact hB1 u
  have hCχ0 : 0 ≤ Cχ / δ := (norm_nonneg _).trans (hCχ 0)
  have gH : R26P10GP y τ (fun u => r26t8a_Hj chi y δ h j u) :=
    r26t8a_p10a_gp_of_bound H.hb zero_le_one (fun u _ => by
      rw [one_mul, abs_of_nonneg (norm_nonneg _)]; exact r26t8a_Hj_bound hchi y δ j u)
  have gDj : R26P10GP y (τ + 1) (fun u => r26t8a_Dj chi y δ h j u) := by
    have g1 := r26t8a_p10a_gp_add H.hdb
      (r26t8a_p10a_gp_of_bound H.hb1 hCχ0 (φ := fun u => ‖h u‖) (ψ := fun u => Cχ / δ * ‖h u‖)
        (fun u _ => by rw [abs_of_nonneg (by positivity), abs_of_nonneg (norm_nonneg _)]))
    exact r26t8a_p10a_gp_of_bound g1 zero_le_one (fun u _ => by
      have := r26t8a_Dj_bound hchi y hδ hCχ (h := h) j u
      rw [one_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (mul_nonneg hCχ0 (norm_nonneg _)))]
      exact this)
  have hIdc := r26t8a_Dj_continuousOn hchi y δ H.C1 j
  have I1 : Integrable (fun u => fderiv ℝ Γ u (EuclideanSpace.single j 1) * r26t8a_Hj chi y δ h j u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd hτ0 (by linarith) ?_ ?_
    · exact r26t8a_p10a_gp_of_bound gH (B := B1) hB10
        (fun u _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hD u) (abs_nonneg _))
    · exact (hdc.mul hHc).aestronglyMeasurable
  have I2 : Integrable (fun u => Γ u * r26t8a_Dj chi y δ h j u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ + 1) hd (by linarith) (by linarith) ?_ ?_
    · exact r26t8a_p10a_gp_of_bound gDj (B := B0) hB00 (fun u _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB0 u) (abs_nonneg _))
    · exact r26t8a_p10a_aesm hd y (hGc.continuousOn.mul hIdc)
  have I3 : Integrable (fun u => Γ u * r26t8a_Hj chi y δ h j u) := by
    refine r26t8a_p10a_gp_integrable (y := y) (τ := τ) hd hτ0 (by linarith) ?_ ?_
    · exact r26t8a_p10a_gp_of_bound gH (B := B0) hB00 (fun u _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB0 u) (abs_nonneg _))
    · exact (hGc.mul hHc).aestronglyMeasurable
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := EuclideanSpace.single j 1)
    (f := Γ) (g := r26t8a_Hj chi y δ h j) I1
    (by simpa only [r26t8a_fderiv_Hj hchi hδ H.C1 j] using I2) I3
    (fun u _ => (hΓ.differentiable (by simp)) u)
    (fun u _ => (r26t8a_hasFDerivAt_Hj hchi hδ H.C1 j u).differentiableAt)
  simp only [r26t8a_fderiv_Hj hchi hδ H.C1 j] at key
  exact ⟨I2, I1, key⟩

end HRS.MS.R26T8A
