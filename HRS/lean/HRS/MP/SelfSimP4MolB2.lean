import HRS.MP.SelfSimP4MolB1

/-!
# MPP4MOL stage 5a (7): bounds, derivative and weighted integrability of `u = G_v * ν`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_mol_le (hv : 0 < v) [IsProbabilityMeasure ν] (x : EucConfig d N) :
    p4Mol v ν x ≤ p4m_cst d N v := by
  unfold p4Mol
  calc ∫ y, p4Gauss d N v (x - y) ∂ν ≤ ∫ _y, p4m_cst d N v ∂ν :=
        integral_mono (p4m_integrable_gauss_sub hv ν x) (integrable_const _) fun y => p4m_gauss_le hv _
    _ = p4m_cst d N v := by simp

theorem p4m_mol_pos (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (x : EucConfig d N) :
    0 < p4Mol v ν x :=
  lt_of_lt_of_le (by have := p4m_cst_pos (d := d) (N := N) hv; positivity) (p4m_mol_lower hv hm x)

theorem p4m_mol_abs_log_le (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) (x : EucConfig d N) :
    |Real.log (p4Mol v ν x)| ≤ |Real.log (p4m_cst d N v)| + (p4m_q x + ∫ y, p4m_q y ∂ν) / v := by
  have hc := p4m_cst_pos (d := d) (N := N) hv
  have hpos := p4m_mol_pos hv hm x
  have hM : 0 ≤ ∫ y, p4m_q y ∂ν := integral_nonneg fun y => p4m_q_nonneg y
  have hq := p4m_q_nonneg x
  have hup := Real.log_le_log hpos (p4m_mol_le hv x)
  have hlow0 : 0 < p4m_cst d N v * Real.exp (-(p4m_q x + ∫ y, p4m_q y ∂ν) / v) := mul_pos hc (Real.exp_pos _)
  have hl := p4m_mol_lower hv hm x
  have hlo := Real.log_le_log hlow0 hl
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hlo
  have hpos' : 0 ≤ (p4m_q x + ∫ y, p4m_q y ∂ν) / v := div_nonneg (add_nonneg hq hM) hv.le
  have e : -(p4m_q x + ∫ y, p4m_q y ∂ν) / v = -((p4m_q x + ∫ y, p4m_q y ∂ν) / v) := by ring
  rw [e] at hlo
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (p4m_cst d N v))]
  · linarith [le_abs_self (Real.log (p4m_cst d N v))]

/-- Product integrability of kernels of the form `k(x - y) m(y)`. -/
theorem p4m_prod_integrable [IsFiniteMeasure ν] {k : EucConfig d N → ℝ} {m : EucConfig d N → ℝ}
    (hk : Integrable k volume) (hm : Integrable m ν) :
    Integrable (fun p : EucConfig d N × EucConfig d N => m p.2 * k (p.1 - p.2)) ((volume : Measure (EucConfig d N)).prod ν) :=
  Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hm hk

/-- The weighted integrability `∫ (1 + q) ∫ E_b(x - y) dν dx < ∞`. -/
theorem p4m_integrable_weight [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x => (1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν) volume := by
  have hE := p4m_integrable_E (d := d) (N := N) hb
  have hqE := p4m_integrable_poly_E (d := d) (N := N) hb 1
  have h1 := p4m_prod_integrable (ν := ν) hE (integrable_const (1 : ℝ))
  have h2 := p4m_prod_integrable (ν := ν) hqE (integrable_const (1 : ℝ))
  have h3 := p4m_prod_integrable (ν := ν) hE hm
  have hbd := (h1.add (h2.const_mul 2)).add (h3.const_mul 2)
  have hF : Integrable (fun p : EucConfig d N × EucConfig d N => (1 + p4m_q p.1) * p4m_E b (p.1 - p.2))
      ((volume : Measure (EucConfig d N)).prod ν) := by
    refine hbd.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((continuous_const.add (p4m_continuous_q.comp continuous_fst)).mul
        ((p4m_continuous_E b).comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
    · have hq1 := p4m_q_nonneg p.1
      have hE0 := p4m_E_pos (d := d) (N := N) b (p.1 - p.2)
      have hq2 := p4m_q_nonneg p.2
      have hq3 := p4m_q_nonneg (p.1 - p.2)
      have hle : p4m_q p.1 ≤ 2 * p4m_q (p.1 - p.2) + 2 * p4m_q p.2 := by
        have := p4m_q_add_le (p.1 - p.2) p.2
        simpa using this
      rw [Real.norm_of_nonneg (by positivity)]
      simp only [Pi.add_apply, one_mul, pow_one]
      nlinarith [mul_le_mul_of_nonneg_right hle hE0.le]
  have := hF.integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [integral_const_mul]

end

end HRS.MP.SelfSimP4Mol
