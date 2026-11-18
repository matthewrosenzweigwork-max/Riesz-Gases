import HRS.MS.R26T8AP05b
import HRS.MS.R26T8AP03d

/-!
# S8.2 local Newton layer, packet T8A.P05 (part c): the nested jet of the annular Newton integral as an integral over `u = z - w`
`r26t8a_conv_formula`: for `|z| <= 4R`, the nested jet equals `int Kk(u) . D^p_Y D^q_w (annulus * midPair F)(Y, z-u) du`, with
`Kk = chi(u/(2 r1)) (K(u) - kappa)`, `r1 = 6R+1` (for `q >= 1` an arbitrary constant `kappa` may be subtracted: `D^q` kills constants).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

def r26t8a_Kk (chi : Euc d → ℝ) (nu kappa r1 : ℝ) (u : Euc d) : ℝ :=
  chi ((1 / (2 * r1)) • u) * (newtonKernel d nu u - kappa)

theorem r26t8a_Kk_eq {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {nu kappa r1 : ℝ} (hr1 : 0 < r1) {u : Euc d}
    (hu : ‖u‖ ≤ 2 * r1) : r26t8a_Kk chi nu kappa r1 u = newtonKernel d nu u - kappa := by
  unfold r26t8a_Kk
  have : ‖(1 / (2 * r1)) • u‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  rw [hchi.2.2.2.1 _ this, one_mul]

theorem r26t8a_Kk_integrable (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (nu kappa : ℝ) {r1 : ℝ}
    (hr1 : 0 < r1) : Integrable (r26t8a_Kk chi nu kappa r1) := by
  set H := r26t8a_Kk chi nu kappa r1 with hH
  have hzero : ∀ u : Euc d, ¬ ‖u‖ < 5 * r1 → H u = 0 := by
    intro u hu
    push Not at hu
    have : 2 ≤ ‖(1 / (2 * r1)) • u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, le_inv_mul_iff₀ (by positivity)]
      linarith
    simp only [hH, r26t8a_Kk, hchi.2.2.2.2 _ this, zero_mul]
  have hind : H = (Metric.ball (0 : Euc d) (5 * r1)).indicator H := by
    funext u
    by_cases h : u ∈ Metric.ball (0 : Euc d) (5 * r1)
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hzero u (by simpa using h)]
  rw [hind, integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  have hK := r26t8a_K_integrableOn hd nu (5 * r1)
  have hc : IntegrableOn (fun _ : Euc d => kappa) (Metric.ball 0 (5 * r1)) :=
    integrableOn_const (Metric.isBounded_ball.measure_lt_top.ne)
  have hm : Measurable H :=
    (hchi.1.continuous.comp (continuous_const_smul _)).measurable.mul ((r26t8a_K_measurable nu).sub_const kappa)
  refine Integrable.mono' (hK.sub hc).norm hm.aestronglyMeasurable.restrict (Eventually.of_forall fun u => ?_)
  rw [hH, r26t8a_Kk, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hchi.2.2.1 _).1]
  exact (hchi.2.2.1 _).2

/-- Slice jets in the second variable. -/
theorem r26t8a_slice_jet_inr {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Θ : Euc d × Euc d → V} {i : ℕ}
    (hΘ : ContDiff ℝ (i : WithTop ℕ∞) Θ) (Y w : Euc d) :
    iteratedFDeriv ℝ i (fun w' => Θ (Y, w')) w =
      (iteratedFDeriv ℝ i Θ (Y, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
  have h1 : (fun w' : Euc d => Θ (Y, w')) = (fun v : Euc d × Euc d => Θ (v + (Y, 0))) ∘
      (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) := by
    funext w'; simp [Prod.mk_add_mk]
  have hf' : ContDiff ℝ (i : WithTop ℕ∞) (fun v : Euc d × Euc d => Θ (v + (Y, 0))) :=
    hΘ.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) hf' w le_rfl]
  rw [iteratedFDeriv_comp_add_right]
  simp

end HRS.MS.R26T8A
