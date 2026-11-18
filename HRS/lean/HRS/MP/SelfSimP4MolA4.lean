import HRS.MP.SelfSimP4MolA3

/-!
# MPP4MOL stage 5a (4): the second moment of the Gaussian and translation invariance
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_continuous_gauss (v : ℝ) : Continuous (p4Gauss d N v : EucConfig d N → ℝ) :=
  (p4m_contDiff_gauss (n := 0) v).continuous

theorem p4m_continuous_coord (k : Fin N × Fin d) :
    Continuous (fun w : EucConfig d N => w k.1 k.2) := by
  have := (p4InnerL (configBasis d N k)).continuous
  exact this.congr fun w => p4m_inner_single_left w k

theorem p4m_coord_abs_le (w : EucConfig d N) (k : Fin N × Fin d) : |w k.1 k.2| ≤ 1 + p4m_q w := by
  have h := p4m_coord_sq_le w k
  have := p4m_q_nonneg w
  nlinarith [sq_abs (w k.1 k.2), abs_nonneg (w k.1 k.2)]

theorem p4m_integral_coord_sq_gauss {v : ℝ} (hv : 0 < v) (k : Fin N × Fin d) :
    ∫ w : EucConfig d N, p4Gauss d N v w * (w k.1 k.2) ^ 2 = v := by
  have hG := p4m_continuous_gauss (d := d) (N := N) v
  have hc := p4m_continuous_coord (d := d) (N := N) k
  have hint1 := p4m_integrable_poly_gauss (d := d) (N := N) hv 1
  have hint0 := p4m_integrable_poly_gauss (d := d) (N := N) hv 0
  have hf : ∀ x ∈ tsupport (fun w : EucConfig d N => p4InnerL (configBasis d N k) w),
      DifferentiableAt ℝ (p4Gauss d N v : EucConfig d N → ℝ) x := fun x _ =>
    ((p4m_contDiff_gauss (n := 1) v).differentiable (by norm_num)) x
  have hg : ∀ x ∈ tsupport (p4Gauss d N v : EucConfig d N → ℝ),
      DifferentiableAt ℝ (fun w : EucConfig d N => p4InnerL (configBasis d N k) w) x := fun x _ =>
    (p4InnerL (configBasis d N k)).differentiableAt
  have hder : ∀ x : EucConfig d N, fderiv ℝ (fun w : EucConfig d N => p4InnerL (configBasis d N k) w) x
      (configBasis d N k) = 1 := by
    intro x
    rw [ContinuousLinearMap.fderiv, p4m_inner_single]
    simp [configBasis]
  have hcoord : ∀ w : EucConfig d N, p4InnerL (configBasis d N k) w = w k.1 k.2 := fun w =>
    p4m_inner_single_left w k
  have hDG : ∀ x : EucConfig d N, fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) x (configBasis d N k) =
      -(1 / v) * p4Gauss d N v x * x k.1 k.2 := by
    intro x
    rw [p4m_fderiv_gauss hv]
    simp [p4m_inner_single]
  have hmeas2 : AEStronglyMeasurable (fun w : EucConfig d N => p4Gauss d N v w * (w k.1 k.2) ^ 2) volume :=
    (hG.mul (hc.pow 2)).aestronglyMeasurable
  have hI1 : Integrable (fun w : EucConfig d N => p4Gauss d N v w * (w k.1 k.2) ^ 2) volume := by
    refine hint1.mono' hmeas2 (Filter.Eventually.of_forall fun w => ?_)
    have := p4m_gauss_pos hv w
    rw [Real.norm_of_nonneg (by positivity), pow_one]
    have h := mul_le_mul_of_nonneg_left (p4m_coord_sq_le w k) this.le
    linarith [mul_comm (p4m_q w) (p4Gauss d N v w)]
  have hI0 : Integrable (fun w : EucConfig d N => p4Gauss d N v w * (w k.1 k.2)) volume := by
    refine ((hint0.add hint1).mono' (hG.mul hc).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_))
    have := p4m_gauss_pos hv w
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos this]
    simp only [pow_zero, one_mul, pow_one, Pi.add_apply]
    nlinarith [p4m_coord_abs_le w k]
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (EucConfig d N))) (f := (p4Gauss d N v : EucConfig d N → ℝ))
    (g := fun w : EucConfig d N => p4InnerL (configBasis d N k) w) (v := configBasis d N k)
    (by
      simp only [hDG, hcoord]
      refine (hI1.const_mul (-(1 / v))).congr (Filter.Eventually.of_forall fun w => ?_)
      simp only; ring)
    (by simp only [hder]; simpa using hint0)
    (by simp only [hcoord]; exact hI0) hf hg
  simp only [hder, hDG] at key
  simp only [hcoord, mul_one] at key
  have e : ∀ w : EucConfig d N, -(1 / v) * p4Gauss d N v w * w k.1 k.2 * w k.1 k.2 =
      -(1 / v) * (p4Gauss d N v w * (w k.1 k.2) ^ 2) := fun w => by ring
  simp only [e, integral_const_mul, p4m_integral_gauss hv, neg_neg] at key
  field_simp at key
  linarith

theorem p4m_integral_q_gauss {v : ℝ} (hv : 0 < v) :
    ∫ w : EucConfig d N, p4m_q w * p4Gauss d N v w = ((N * d : ℕ) : ℝ) * v := by
  have e : ∀ w : EucConfig d N, p4m_q w * p4Gauss d N v w =
      ∑ k : Fin N × Fin d, p4Gauss d N v w * (w k.1 k.2) ^ 2 := fun w => by
    rw [p4m_q_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hI : ∀ k : Fin N × Fin d, Integrable (fun w : EucConfig d N => p4Gauss d N v w * (w k.1 k.2) ^ 2) volume := by
    intro k
    have hint1 := p4m_integrable_poly_gauss (d := d) (N := N) hv 1
    refine hint1.mono' ((p4m_continuous_gauss v).mul ((p4m_continuous_coord k).pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    have := p4m_gauss_pos hv w
    rw [Real.norm_of_nonneg (by positivity), pow_one]
    have h := mul_le_mul_of_nonneg_left (p4m_coord_sq_le w k) this.le
    linarith [mul_comm (p4m_q w) (p4Gauss d N v w)]
  simp only [e]
  rw [integral_finset_sum _ fun k _ => hI k]
  simp only [p4m_integral_coord_sq_gauss hv]
  simp [mul_comm]

end HRS.MP.SelfSimP4Mol
