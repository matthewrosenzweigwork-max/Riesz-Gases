import HRS.MP.SelfSimP4MolA5

/-!
# MPP4MOL stage 5a (6): the mollified density `u = G_v * ν` of a probability measure with a second moment
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_q_sub_le (a b : EucConfig d N) : p4m_q (a - b) ≤ 2 * p4m_q a + 2 * p4m_q b := by
  simp only [p4m_q_eq]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.sub_apply, PiLp.sub_apply]
  nlinarith [sq_nonneg (a k.1 k.2 + b k.1 k.2)]

theorem p4m_q_add_le (a b : EucConfig d N) : p4m_q (a + b) ≤ 2 * p4m_q a + 2 * p4m_q b := by
  have := p4m_q_sub_le a (-b)
  simpa [sub_neg_eq_add, p4m_q_neg] using this

theorem p4m_measurable_q : Measurable (p4m_q : EucConfig d N → ℝ) := p4m_continuous_q.measurable

theorem p4m_integrable_q_sub {ν : Measure (EucConfig d N)} [IsFiniteMeasure ν]
    (hm : Integrable p4m_q ν) (x : EucConfig d N) : Integrable (fun y => p4m_q (x - y)) ν := by
  have h := (integrable_const (2 * p4m_q x)).add (hm.const_mul 2)
  refine h.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (p4m_continuous_q.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (p4m_q_nonneg _)]
    exact p4m_q_sub_le x y

theorem p4m_integrable_gauss_sub {v : ℝ} (hv : 0 < v) (ν : Measure (EucConfig d N)) [IsFiniteMeasure ν]
    (x : EucConfig d N) : Integrable (fun y => p4Gauss d N v (x - y)) ν :=
  Integrable.of_bound ((p4m_continuous_gauss v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (p4m_cst d N v) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (p4m_gauss_pos hv _).le]; exact p4m_gauss_le hv _)

/-- Jensen lower bound for the mollified density. -/
theorem p4m_mol_lower {v : ℝ} (hv : 0 < v) {ν : Measure (EucConfig d N)} [IsProbabilityMeasure ν]
    (hm : Integrable p4m_q ν) (x : EucConfig d N) :
    p4m_cst d N v * Real.exp (-(p4m_q x + ∫ y, p4m_q y ∂ν) / v) ≤ p4Mol v ν x := by
  have hc := p4m_cst_pos (d := d) (N := N) hv
  set f : EucConfig d N → ℝ := fun y => -(p4m_q (x - y)) / (2 * v) with hf
  have hfc : Continuous f :=
    ((p4m_continuous_q.comp (continuous_const.sub continuous_id)).neg).div_const _
  have hfi : Integrable f ν := ((p4m_integrable_q_sub hm x).neg).div_const _
  have hexp : ∀ y, p4Gauss d N v (x - y) = p4m_cst d N v * Real.exp (f y) := fun y => p4m_gauss_eq v _
  have hf0 : ∀ y, f y ≤ 0 := fun y => by
    have := p4m_q_nonneg (x - y)
    have : 0 ≤ p4m_q (x - y) / (2 * v) := by positivity
    simp only [hf, neg_div]; linarith
  have hgi : Integrable (Real.exp ∘ f) ν :=
    Integrable.of_bound (Real.continuous_exp.comp hfc).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun y => by
      simp only [Function.comp_apply]
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (hf0 y))
  have hjensen := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun y => Set.mem_univ (f y)) hfi hgi
  have hmol : p4Mol v ν x = p4m_cst d N v * ∫ y, Real.exp (f y) ∂ν := by
    unfold p4Mol
    simp only [hexp]
    rw [integral_const_mul]
  rw [hmol]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ hjensen) hc.le
  refine Real.exp_le_exp.2 ?_
  have h1 : ∫ y, f y ∂ν = -(∫ y, p4m_q (x - y) ∂ν) / (2 * v) := by
    simp only [hf]
    rw [integral_div, integral_neg]
  have h2 : ∫ y, p4m_q (x - y) ∂ν ≤ 2 * p4m_q x + 2 * ∫ y, p4m_q y ∂ν := by
    have := integral_mono (p4m_integrable_q_sub hm x) ((integrable_const (2 * p4m_q x)).add (hm.const_mul 2))
      (fun y => p4m_q_sub_le x y)
    simp only [Pi.add_apply] at this
    rw [integral_add (integrable_const _) (hm.const_mul 2)] at this
    have e2 : ∫ a, 2 * p4m_q a ∂ν = 2 * ∫ a, p4m_q a ∂ν := integral_const_mul _ _
    rw [e2] at this
    simpa using this
  rw [h1]
  have : -(p4m_q x + ∫ y, p4m_q y ∂ν) / v = -(2 * p4m_q x + 2 * ∫ y, p4m_q y ∂ν) / (2 * v) := by
    field_simp
  rw [this]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end HRS.MP.SelfSimP4Mol
