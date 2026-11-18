import HRS.MS.QMulAux6

/-!
# MS-QMUL, part 7: lower semicontinuity of the weighted `L²` norm under `L²` convergence
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.QMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem qm_lint_sq_eq {f : Euc d → ℂ} (hf : MemLp f 2 volume) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = eLpNorm f 2 volume ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem qm_eLpNorm_eq (f : Euc d → ℂ) (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume = (∫⁻ x, ‖f x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) := by
  rw [qm_lint_sq_eq hf, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem qm_fatou (m : ℕ) {G : Euc d → ℂ} {Gn : ℕ → Euc d → ℂ} (hG : MemLp G 2 volume)
    (hGn : ∀ n, MemLp (Gn n) 2 volume)
    (hconv : Tendsto (fun n => ∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2) atTop (𝓝 0))
    {B : ℕ → ℝ≥0∞} {B0 : ℝ≥0∞}
    (hB : ∀ n, ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖Gn n ξ‖ ^ 2) ≤ B n)
    (hBlim : Tendsto B atTop (𝓝 B0)) :
    ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖G ξ‖ ^ 2) ≤ B0 := by
  have hconv' : Tendsto (fun n => eLpNorm (Gn n - G) 2 volume) atTop (𝓝 0) := by
    have e : ∀ n, eLpNorm (Gn n - G) 2 volume = (∫⁻ ξ, ‖Gn n ξ - G ξ‖ₑ ^ 2) ^ ((1 : ℝ) / 2) :=
      fun n => qm_eLpNorm_eq _ ((hGn n).sub hG)
    simp_rw [e]
    have := ((ENNReal.continuous_rpow_const (y := (1 : ℝ) / 2)).tendsto 0).comp hconv
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    exact this
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (μ := volume) (f := Gn) (g := G)
    (by norm_num) hconv'
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  set F : ℕ → Euc d → ℝ≥0∞ := fun i ξ => ENNReal.ofReal (wt ξ ^ m * ‖Gn (ns i) ξ‖ ^ 2) with hF
  have hFm : ∀ i, AEMeasurable (F i) volume := by
    intro i
    have : AEStronglyMeasurable (fun ξ => wt ξ ^ m * ‖Gn (ns i) ξ‖ ^ 2) volume :=
      (continuous_wt.pow m).aestronglyMeasurable.mul (((hGn (ns i)).aestronglyMeasurable.norm).pow 2)
    exact this.aemeasurable.ennreal_ofReal
  have hlim : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      Tendsto (fun i => F i ξ) atTop (𝓝 (ENNReal.ofReal (wt ξ ^ m * ‖G ξ‖ ^ 2))) := by
    filter_upwards [hae] with ξ hξ
    have h1 : Tendsto (fun i => wt ξ ^ m * ‖Gn (ns i) ξ‖ ^ 2) atTop (𝓝 (wt ξ ^ m * ‖G ξ‖ ^ 2)) :=
      (hξ.norm.pow 2).const_mul _
    exact (ENNReal.continuous_ofReal.tendsto _).comp h1
  have h1 : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖G ξ‖ ^ 2) =
      ∫⁻ ξ, liminf (fun i => F i ξ) atTop := by
    refine lintegral_congr_ae ?_
    filter_upwards [hlim] with ξ hξ
    exact hξ.liminf_eq.symm
  rw [h1]
  refine (lintegral_liminf_le' hFm).trans ?_
  have h2 : Tendsto (fun i => B (ns i)) atTop (𝓝 B0) := hBlim.comp hns.tendsto_atTop
  rw [← h2.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => hB (ns i))

end HRS.MS.QMul
