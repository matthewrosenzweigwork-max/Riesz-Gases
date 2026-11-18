import HRS.MP.SelfSimP4MolG1

/-!
# MPP4MOL stage 5c (12): the weight integral and the logarithm bound
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_weight_integral_le {ν : Measure (EucConfig d N)} [IsProbabilityMeasure ν]
    (hm : Integrable p4m_q ν) {b : ℝ} (hb : 0 < b) :
    ∫ x, (1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν ≤
      (∫ w : EucConfig d N, p4m_E b w) + 2 * (∫ w : EucConfig d N, p4m_q w * p4m_E b w) +
        2 * (∫ w : EucConfig d N, p4m_E b w) * ∫ y, p4m_q y ∂ν := by
  have hE := p4m_integrable_E (d := d) (N := N) hb
  have hqE := p4m_integrable_poly_E (d := d) (N := N) hb 1
  simp only [pow_one] at hqE
  have h1 : Integrable (fun p : EucConfig d N × EucConfig d N => p4m_E b (p.1 - p.2))
      ((volume : Measure (EucConfig d N)).prod ν) :=
    (p4m_prod_integrable (ν := ν) hE (integrable_const (1 : ℝ))).congr
      (Filter.Eventually.of_forall fun p => by simp)
  have h2 : Integrable (fun p : EucConfig d N × EucConfig d N => p4m_q (p.1 - p.2) * p4m_E b (p.1 - p.2))
      ((volume : Measure (EucConfig d N)).prod ν) :=
    (p4m_prod_integrable (ν := ν) hqE (integrable_const (1 : ℝ))).congr
      (Filter.Eventually.of_forall fun p => by simp)
  have h3 : Integrable (fun p : EucConfig d N × EucConfig d N => p4m_q p.2 * p4m_E b (p.1 - p.2))
      ((volume : Measure (EucConfig d N)).prod ν) := p4m_prod_integrable (ν := ν) hE hm
  have hH : Integrable (fun p : EucConfig d N × EucConfig d N => p4m_E b (p.1 - p.2) +
      2 * (p4m_q (p.1 - p.2) * p4m_E b (p.1 - p.2)) + 2 * (p4m_q p.2 * p4m_E b (p.1 - p.2)))
      ((volume : Measure (EucConfig d N)).prod ν) := (h1.add (h2.const_mul 2)).add (h3.const_mul 2)
  have hF : Integrable (fun p : EucConfig d N × EucConfig d N => (1 + p4m_q p.1) * p4m_E b (p.1 - p.2))
      ((volume : Measure (EucConfig d N)).prod ν) := by
    refine hH.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
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
      nlinarith [mul_le_mul_of_nonneg_right hle hE0.le]
  have hτ : ∫ x, (1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν =
      ∫ p, (1 + p4m_q p.1) * p4m_E b (p.1 - p.2) ∂((volume : Measure (EucConfig d N)).prod ν) := by
    rw [integral_prod _ hF]
    simp only [integral_const_mul]
  rw [hτ]
  have hmono : ∫ p, (1 + p4m_q p.1) * p4m_E b (p.1 - p.2) ∂((volume : Measure (EucConfig d N)).prod ν) ≤
      ∫ p, (p4m_E b (p.1 - p.2) + 2 * (p4m_q (p.1 - p.2) * p4m_E b (p.1 - p.2)) +
        2 * (p4m_q p.2 * p4m_E b (p.1 - p.2))) ∂((volume : Measure (EucConfig d N)).prod ν) := by
    refine integral_mono hF hH fun p => ?_
    have hq1 := p4m_q_nonneg p.1
    have hE0 := p4m_E_pos (d := d) (N := N) b (p.1 - p.2)
    have hle : p4m_q p.1 ≤ 2 * p4m_q (p.1 - p.2) + 2 * p4m_q p.2 := by
      have := p4m_q_add_le (p.1 - p.2) p.2
      simpa using this
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_right hle hE0.le]
  refine hmono.trans (le_of_eq ?_)
  rw [integral_prod_symm _ hH]
  have hin : ∀ y : EucConfig d N, ∫ x, (p4m_E b (x - y) + 2 * (p4m_q (x - y) * p4m_E b (x - y)) +
      2 * (p4m_q y * p4m_E b (x - y))) =
      (∫ w : EucConfig d N, p4m_E b w) + 2 * (∫ w : EucConfig d N, p4m_q w * p4m_E b w) +
        2 * (p4m_q y * ∫ w : EucConfig d N, p4m_E b w) := by
    intro y
    have e1 : Integrable (fun x : EucConfig d N => p4m_E b (x - y)) := hE.comp_sub_right y
    have e2 : Integrable (fun x : EucConfig d N => p4m_q (x - y) * p4m_E b (x - y)) :=
      hqE.comp_sub_right y
    have hs1 : Integrable (fun x : EucConfig d N => p4m_E b (x - y) + 2 * (p4m_q (x - y) * p4m_E b (x - y))) :=
      e1.add (e2.const_mul 2)
    have hs2 : Integrable (fun x : EucConfig d N => 2 * (p4m_q y * p4m_E b (x - y))) :=
      (e1.const_mul (p4m_q y)).const_mul 2
    rw [integral_add hs1 hs2, integral_add e1 (e2.const_mul 2), integral_const_mul, integral_const_mul,
      integral_const_mul,
      integral_sub_right_eq_self (fun w : EucConfig d N => p4m_E b w) y,
      integral_sub_right_eq_self (fun w : EucConfig d N => p4m_q w * p4m_E b w) y]
  simp only [hin]
  rw [integral_add (integrable_const _) ((hm.mul_const _).const_mul 2), integral_const, integral_const_mul,
    integral_mul_const]
  simp
  ring

end HRS.MP.SelfSimP4Mol
