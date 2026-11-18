import HRS.MP.SelfSimP4MolB2

/-!
# MPP4MOL stage 5a (8): the derivative of `u = G_v * ν`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_continuous_innerL : Continuous (p4InnerL : EucConfig d N → EucConfig d N →L[ℝ] ℝ) := by
  unfold p4InnerL
  refine continuous_finset_sum _ fun i _ => ?_
  refine Continuous.clm_comp ?_ continuous_const
  exact (innerSL ℝ).continuous.comp (continuous_apply i)

/-- Uniform bound on `‖DG_v‖`. -/
theorem p4m_D1_bound {v : ℝ} (hv : 0 < v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EucConfig d N, ‖fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) w‖ ≤ C := by
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  refine ⟨(1 / v) * N * (C0 + C1), by positivity, fun w => ?_⟩
  have h1 := p4m_D1_norm_le hv w
  have hG := p4m_gauss_pos (d := d) (N := N) hv w
  have hq := p4m_norm_sq_le_q w
  have h0 := hb0 w
  have h1' := hb1 w
  simp only [pow_zero, one_mul, pow_one] at h0 h1'
  have hw0 := norm_nonneg w
  have hw1 : ‖w‖ ≤ 1 + p4m_q w := by nlinarith
  have : p4Gauss d N v w * ‖w‖ ≤ C0 + C1 := by nlinarith [mul_le_mul_of_nonneg_left hw1 hG.le]
  calc _ ≤ _ := h1
    _ = (1 / v) * N * (p4Gauss d N v w * ‖w‖) := by ring
    _ ≤ _ := by gcongr

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_hasFDerivAt_mol (hv : 0 < v) [IsProbabilityMeasure ν] (x₀ : EucConfig d N) :
    HasFDerivAt (p4Mol v ν)
      (∫ y, fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) (x₀ - y) ∂ν) x₀ := by
  obtain ⟨C, hC0, hC⟩ := p4m_D1_bound (d := d) (N := N) hv
  have hG1 : ContDiff ℝ 1 (p4Gauss d N v : EucConfig d N → ℝ) := p4m_contDiff_gauss v
  have hderivc : Continuous (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) := hG1.continuous_fderiv (by norm_num)
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (𝕜 := ℝ) (s := Set.univ)
    (F := fun x y => p4Gauss d N v (x - y))
    (F' := fun x y => fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) (x - y)) (x₀ := x₀) (bound := fun _ => C)
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => ((p4m_continuous_gauss v).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (p4m_integrable_gauss_sub hv ν x₀)
    (hderivc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x _ => hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun y x _ => by
      have h1 := (p4m_contDiff_gauss (n := 1) v).differentiable (by norm_num) (x - y)
      have h2 := h1.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)
      rw [ContinuousLinearMap.comp_id] at h2
      exact h2)
  exact this

theorem p4m_fderiv_mol_apply (hv : 0 < v) [IsProbabilityMeasure ν] (x h : EucConfig d N) :
    fderiv ℝ (p4Mol v ν) x h =
      ∫ y, (-(1 / v) * p4Gauss d N v (x - y)) * p4InnerL (x - y) h ∂ν := by
  obtain ⟨C, hC0, hC⟩ := p4m_D1_bound (d := d) (N := N) hv
  have hG1 : ContDiff ℝ 1 (p4Gauss d N v : EucConfig d N → ℝ) := p4m_contDiff_gauss v
  have hderivc : Continuous (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) := hG1.continuous_fderiv (by norm_num)
  have hint : Integrable (fun y => fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) (x - y)) ν :=
    Integrable.of_bound (hderivc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => hC _)
  rw [(p4m_hasFDerivAt_mol hv x).fderiv, ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [p4m_fderiv_gauss hv, ContinuousLinearMap.smul_apply, smul_eq_mul]

end

end HRS.MP.SelfSimP4Mol
