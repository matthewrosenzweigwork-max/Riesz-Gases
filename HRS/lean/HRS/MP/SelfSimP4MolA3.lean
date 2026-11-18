import HRS.MP.SelfSimP4MolA2

/-!
# MPP4MOL stage 5a (3): Gaussian integrals on `(ℝ^d)^N`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- `e^{-b q}`. -/
def p4m_E (b : ℝ) (w : EucConfig d N) : ℝ := Real.exp (-b * p4m_q w)

theorem p4m_E_eq_prod (b : ℝ) (w : EucConfig d N) :
    p4m_E b w = ∏ i, Real.exp (-b * ‖w i‖ ^ 2) := by
  simp only [p4m_E, p4m_q, neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem p4m_E_pos (b : ℝ) (w : EucConfig d N) : 0 < p4m_E b w := Real.exp_pos _

theorem p4m_continuous_E (b : ℝ) : Continuous (p4m_E b : EucConfig d N → ℝ) :=
  Real.continuous_exp.comp (continuous_const.mul p4m_continuous_q)

theorem p4m_integrable_E {b : ℝ} (hb : 0 < b) : Integrable (p4m_E b : EucConfig d N → ℝ) volume := by
  have h1 : ∀ i : Fin N, Integrable (fun z : Euc d => Real.exp (-b * ‖z‖ ^ 2)) volume := by
    intro i
    refine Integrable.of_integral_ne_zero ?_
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
    positivity
  have := Integrable.fintype_prod (𝕜 := ℝ) (ι := Fin N) (E := Euc d)
    (f := fun _ z => Real.exp (-b * ‖z‖ ^ 2)) (μ := fun _ => volume) h1
  have e : (p4m_E b : EucConfig d N → ℝ) = fun w => ∏ i, Real.exp (-b * ‖w i‖ ^ 2) :=
    funext (p4m_E_eq_prod b)
  rw [e]
  exact this

theorem p4m_integral_E {b : ℝ} (hb : 0 < b) :
    ∫ w : EucConfig d N, p4m_E b w = ((Real.pi / b) ^ ((d : ℝ) / 2)) ^ N := by
  have e : (p4m_E b : EucConfig d N → ℝ) = fun w => ∏ i, Real.exp (-b * ‖w i‖ ^ 2) :=
    funext (p4m_E_eq_prod b)
  rw [e]
  have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (ι := Fin N) (E := fun _ => Euc d)
    (f := fun _ z => Real.exp (-b * ‖z‖ ^ 2)) (μ := fun _ => volume)
  simp only [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem p4m_E_poly_bound {b : ℝ} (hb : 0 < b) (m : ℕ) (w : EucConfig d N) :
    p4m_q w ^ m * Real.exp (-(b / 2) * p4m_q w) ≤ (m.factorial : ℝ) * (2 / b) ^ m := by
  have h := p4m_gauss_poly_bound (d := d) (N := N) (v := 1 / b) (by positivity) m w
  have e : Real.exp (-(p4m_q w) / (2 * (1 / b))) = Real.exp (-(b / 2) * p4m_q w) := by
    congr 1; field_simp
  rw [e] at h
  have e2 : 2 * (1 / b) = 2 / b := by ring
  rwa [e2] at h

theorem p4m_integrable_poly_E {b : ℝ} (hb : 0 < b) (m : ℕ) :
    Integrable (fun w : EucConfig d N => p4m_q w ^ m * p4m_E b w) volume := by
  have h1 := (p4m_integrable_E (d := d) (N := N) (half_pos hb)).const_mul ((m.factorial : ℝ) * (2 / b) ^ m)
  refine h1.mono' ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact ((p4m_continuous_q.pow m).mul (p4m_continuous_E b)).aestronglyMeasurable
  · have hq := p4m_q_nonneg w
    rw [Real.norm_of_nonneg (by have := p4m_E_pos (d := d) (N := N) b w; positivity)]
    have e : p4m_E b w = Real.exp (-(b / 2) * p4m_q w) * p4m_E (b / 2) w := by
      simp only [p4m_E, ← Real.exp_add]; congr 1; ring
    rw [e, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (p4m_E_poly_bound hb m w) (p4m_E_pos _ _).le

theorem p4m_gauss_eq_E {v : ℝ} (hv : 0 < v) (w : EucConfig d N) :
    p4Gauss d N v w = p4m_cst d N v * p4m_E (1 / (2 * v)) w := by
  rw [p4m_gauss_eq]; congr 2; simp only [neg_div, neg_mul, one_div, mul_inv_rev]; ring

theorem p4m_integrable_poly_gauss {v : ℝ} (hv : 0 < v) (m : ℕ) :
    Integrable (fun w : EucConfig d N => p4m_q w ^ m * p4Gauss d N v w) volume := by
  have := (p4m_integrable_poly_E (d := d) (N := N) (b := 1 / (2 * v)) (by positivity) m).const_mul
    (p4m_cst d N v)
  refine this.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [p4m_gauss_eq_E hv]; ring

theorem p4m_integrable_gauss {v : ℝ} (hv : 0 < v) :
    Integrable (p4Gauss d N v : EucConfig d N → ℝ) volume := by
  simpa using p4m_integrable_poly_gauss (d := d) (N := N) hv 0

theorem p4m_integral_gauss {v : ℝ} (hv : 0 < v) : ∫ w : EucConfig d N, p4Gauss d N v w = 1 := by
  have e : (p4Gauss d N v : EucConfig d N → ℝ) = fun w => p4m_cst d N v * p4m_E (1 / (2 * v)) w :=
    funext (p4m_gauss_eq_E hv)
  rw [e, integral_const_mul, p4m_integral_E (by positivity)]
  unfold p4m_cst
  have h2 : Real.pi / (1 / (2 * v)) = 2 * Real.pi * v := by field_simp
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_add (by positivity)]
  have : (-(((N * d : ℕ) : ℝ)) / 2 + (d : ℝ) / 2 * (N : ℝ)) = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

end HRS.MP.SelfSimP4Mol
