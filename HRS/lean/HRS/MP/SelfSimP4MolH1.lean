import HRS.MP.SelfSimP4MolG3

/-!
# MPP4MOL stage 5c (14): the free energy density is integrable, and `R → ∞` for the cut-off free energy
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_mol_eq_E {v : ℝ} (hv : 0 < v) (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν]
    (x : EucConfig d N) :
    p4Mol v ν x = p4m_cst d N v * ∫ y, p4m_E (1 / (2 * v)) (x - y) ∂ν := by
  unfold p4Mol
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [p4m_gauss_eq_E hv]

theorem p4m_integrable_q_mol {v : ℝ} (hv : 0 < v) {ν : Measure (EucConfig d N)} [IsProbabilityMeasure ν]
    (hm : Integrable p4m_q ν) : Integrable (fun x => (1 + p4m_q x) * p4Mol v ν x) volume := by
  have := (p4m_integrable_weight hm (b := 1 / (2 * v)) (by positivity)).const_mul (p4m_cst d N v)
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [p4m_mol_eq_E hv ν x]
  ring

theorem p4m_integrable_mol {v : ℝ} (hv : 0 < v) {ν : Measure (EucConfig d N)} [IsProbabilityMeasure ν]
    (hm : Integrable p4m_q ν) : Integrable (p4Mol v ν : EucConfig d N → ℝ) volume := by
  refine (p4m_integrable_q_mol hv hm).mono' (p4m_cont_u hv hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hu := p4m_mol_pos hv hm x
  have hq := p4m_q_nonneg x
  rw [Real.norm_of_nonneg hu.le]
  nlinarith

section
variable {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {V W : ℝ → EucConfig d N → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem P4MolData.Phi_bound (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ) (s : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |p4m_Phi v θ μ V s x| ≤ A * ((1 + p4m_q x) * p4Mol v (μ s) x) := by
  haveI := h.prob s
  have hM0 : 0 ≤ M := (integral_nonneg fun y => p4m_q_nonneg y).trans (h.hM s)
  have hCV : 0 ≤ CV := by
    have := h.Vg s 0
    have h0 : p4m_q (0 : EucConfig d N) = 0 := by simp [p4m_q]
    rw [h0] at this
    nlinarith [abs_nonneg (V s 0)]
  refine ⟨|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ, by positivity, fun x => ?_⟩
  have hu := h.pos_u hv s x
  have hl := p4m_mol_abs_log_le hv (h.hm s) x
  have hq := p4m_q_nonneg x
  have hVx := h.Vg s x
  have hMs := h.hM s
  unfold p4m_Phi
  have e : p4Mol v (μ s) x * Real.log (p4Mol v (μ s) x) + p4Mol v (μ s) x * V s x / θ =
      p4Mol v (μ s) x * (Real.log (p4Mol v (μ s) x) + V s x / θ) := by ring
  rw [e, abs_mul, abs_of_pos hu]
  have h1 : |Real.log (p4Mol v (μ s) x) + V s x / θ| ≤ |Real.log (p4Mol v (μ s) x)| + |V s x| / θ := by
    calc _ ≤ |Real.log (p4Mol v (μ s) x)| + |V s x / θ| := abs_add_le _ _
      _ = _ := by rw [abs_div, abs_of_pos hθ]
  have h2 : (p4m_q x + ∫ y, p4m_q y ∂(μ s)) / v ≤ (1 + M) * (1 + p4m_q x) / v := by
    gcongr
    nlinarith [mul_nonneg hM0 hq]
  have h3 : |V s x| / θ ≤ CV * (1 + p4m_q x) / θ := by gcongr
  have h4 : (1 + M) * (1 + p4m_q x) / v = (1 + M) / v * (1 + p4m_q x) := by ring
  have h5 : CV * (1 + p4m_q x) / θ = CV / θ * (1 + p4m_q x) := by ring
  have hc : 0 ≤ |Real.log (p4m_cst d N v)| := abs_nonneg _
  have hfin : |Real.log (p4Mol v (μ s) x) + V s x / θ| ≤
      (|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ) * (1 + p4m_q x) := by
    nlinarith [mul_nonneg hc hq]
  calc p4Mol v (μ s) x * |Real.log (p4Mol v (μ s) x) + V s x / θ|
      ≤ p4Mol v (μ s) x * ((|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ) * (1 + p4m_q x)) := by
        gcongr
    _ = _ := by ring

theorem P4MolData.integrable_Phi (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ) (s : ℝ) :
    Integrable (fun x => p4m_Phi v θ μ V s x) volume := by
  haveI := h.prob s
  obtain ⟨A, hA0, hA⟩ := h.Phi_bound hv hθ s
  refine ((p4m_integrable_q_mol hv (h.hm s)).const_mul A).mono'
    ((h.cont_Phi hv).comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact hA x

/-- `F_R(s) → F(s)` as the cut-off is removed. -/
theorem P4MolData.tendsto_free (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ) (s : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, p4m_chi ((n : ℝ) + 1) x * p4m_Phi v θ μ V s x) atTop
      (𝓝 (∫ x, p4m_Phi v θ μ V s x)) := by
  haveI := h.prob s
  obtain ⟨A, hA0, hA⟩ := h.Phi_bound hv hθ s
  refine tendsto_integral_of_dominated_convergence (fun x => A * ((1 + p4m_q x) * p4Mol v (μ s) x)) ?_
    ((p4m_integrable_q_mol hv (h.hm s)).const_mul A) ?_ ?_
  · intro n
    exact ((p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous.mul
      ((h.cont_Phi hv).comp (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p4m_chi_nonneg _ _)]
    calc p4m_chi ((n : ℝ) + 1) x * |p4m_Phi v θ μ V s x| ≤ 1 * |p4m_Phi v θ μ V s x| := by
          gcongr
          exact p4m_chi_le_one _ _
      _ ≤ _ := by rw [one_mul]; exact hA x
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_gt (p4m_q x)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    have hq := p4m_q_nonneg x
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [p4m_chi_eq_one (R := (n : ℝ) + 1) (by positivity) (by nlinarith), one_mul]

end

end HRS.MP.SelfSimP4Mol
