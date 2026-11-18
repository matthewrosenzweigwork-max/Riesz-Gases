import HRS.MS.S111X1E9
import HRS.MS.WsStatAux6
import HRS.MS.MovThermAux1

/-!
# S11.1 X1, thermal facts: `EnData` for the stationary model
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem hdrift_aux (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) (B : Euc d → Euc d)
    (hBdef : B = fun x => (-β) • gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x)
    (x : Euc d) :
    meanFieldDriftW (quadraticGradientDyn d s a β) ρ x = β⁻¹ • B x - a • x := by
  unfold meanFieldDriftW
  have hQ : (a • (1 : Matrix (Fin d) (Fin d) ℝ)).IsSymm := by unfold Matrix.IsSymm; simp
  rw [HRS.MS.S21.s21_dyn_eq]
  simp only
  rw [HRS.MS.S21.s21_matVec_neg_one, HRS.MS.Adj.ad_gradient_quadV hQ 0 x, HRS.MS.S21.s21_matVec_smul_one, add_zero]
  have hU := HRS.MS.S21.s21_gradU_eq hd hs0 hsd ha hβ hρ x
  rw [hU]
  have : B x = (-β) • gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x := by
    rw [hBdef]
  rw [this, smul_smul]
  have e : β⁻¹ * -β = -1 := by field_simp
  rw [e, neg_one_smul]

theorem enData_of_thermal (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ M : ℝ, EnData d s β ρ M (x1C d s a β ρ) ∧ ∫ x, ρ x = 1 := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hs1 : s + 1 < d := by linarith
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hSch : IsSchwartzDensity ρ := by rw [hρeq]; exact HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ
  obtain ⟨hprob, ψ, hψ⟩ := hSch
  obtain ⟨B, hBdef, hGap, hcb⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρ
  obtain ⟨Mb, hMb⟩ := hcb 0
  have hint : Integrable ρ := hGap.integrable
  -- boundedness of the density
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, ρ x ≤ M := by
    refine ⟨‖ψ.toBoundedContinuousFunction‖, fun x => ?_⟩
    have := ψ.toBoundedContinuousFunction.norm_coe_le_norm x
    have e : ψ.toBoundedContinuousFunction x = ρ x := by rw [← hψ]; rfl
    rw [e] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have hdrift : ∀ x, (x1C d s a β ρ).drift 0 x = β⁻¹ • B x - a • x := fun x =>
    hdrift_aux hd hs0 hsd ha hβ hρ B hBdef x
  have hMT : ∀ v : Euc d, Torus.matVec (x1C d s a β ρ).M.transpose v = -v := by
    intro v
    show Torus.matVec ((-1 : Matrix (Fin d) (Fin d) ℝ).transpose) v = -v
    rw [Matrix.transpose_neg, Matrix.transpose_one]
    exact HRS.MS.S21.s21_matVec_neg_one v
  have hgrad : ∀ r x, gradient ρ x = (β * ρ x) • (x1C d s a β ρ).drift r x := by
    intro r x
    have h1 := hGap.grad x
    have h2 : (x1C d s a β ρ).drift r x = β⁻¹ • B x - a • x := hdrift x
    rw [h2, h1]
    match_scalars <;> field_simp
  have hmom : Integrable (fun x : Euc d => ‖x‖ * ρ x) := by
    refine (hint.add hGap.moment2).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (continuous_norm.mul hGap.smooth.continuous).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg x) (hGap.pos x).le)]
      have := (hGap.pos x).le
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
  have hdg : ∃ c0 : ℝ, ∀ r x, ‖(x1C d s a β ρ).drift r x‖ ≤ c0 * (1 + ‖x‖) := by
    refine ⟨max (β⁻¹ * |Mb|) a, fun r x => ?_⟩
    have h2 : (x1C d s a β ρ).drift r x = β⁻¹ • B x - a • x := hdrift x
    rw [h2]
    have hBx : ‖B x‖ ≤ |Mb| := by
      have := hMb.2 0 le_rfl x
      rw [norm_iteratedFDeriv_zero] at this
      exact this.trans (le_abs_self _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hβ), abs_of_pos ha]
    have h3 : β⁻¹ * ‖B x‖ ≤ β⁻¹ * |Mb| := mul_le_mul_of_nonneg_left hBx (inv_pos.2 hβ).le
    have hm := le_max_left (β⁻¹ * |Mb|) a
    have hm2 := le_max_right (β⁻¹ * |Mb|) a
    nlinarith [norm_nonneg x, abs_nonneg Mb]
  refine ⟨M, ⟨⟨by omega, hs0, hs1, hprob.measurable, hprob.nonneg, hint, hM⟩, hβ, rfl, rfl, fun r => rfl, hMT,
    ?_, hgrad, hmom, hdg⟩, hprob.integral_one⟩
  rw [← hψ]
  exact ψ.smooth 2

end HRS.MS.S111X1
