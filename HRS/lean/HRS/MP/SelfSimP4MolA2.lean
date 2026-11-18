import HRS.MP.SelfSimP4MolA1

/-!
# MPP4MOL stage 5a (2): second derivative of the Gaussian, Gaussian integrals
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_fderiv2_gauss {v : ℝ} (hv : 0 < v) (w h h' : EucConfig d N) :
    fderiv ℝ (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) w h h' =
      (1 / v ^ 2) * p4Gauss d N v w * (p4InnerL w h * p4InnerL w h') -
        (1 / v) * p4Gauss d N v w * p4InnerL h h' := by
  have hG2 : ContDiff ℝ 2 (p4Gauss d N v : EucConfig d N → ℝ) := p4m_contDiff_gauss v
  have hdiff : Differentiable ℝ (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) :=
    (hG2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e1 : fderiv ℝ (fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ)) w h h' =
      fderiv ℝ (fun y => fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) y h') w h := by
    rw [fderiv_clm_apply (hdiff w) (differentiableAt_const h')]
    simp
  have e2 : (fun y => fderiv ℝ (p4Gauss d N v : EucConfig d N → ℝ) y h') =
      fun y => (-(1 / v) * p4Gauss d N v y) * p4InnerL h' y := by
    funext y
    rw [p4m_fderiv_gauss hv]
    simp [p4m_inner_comm]
  rw [e1, e2]
  have hs : HasFDerivAt (fun y => -(1 / v) * (p4Gauss d N v : EucConfig d N → ℝ) y)
      ((-(1 / v)) • ((-(1 / v) * p4Gauss d N v w) • p4InnerL w)) w :=
    (p4m_hasFDerivAt_gauss hv w).const_mul _
  have hp := (p4InnerL h').hasFDerivAt (x := w)
  have := hs.fun_mul hp
  rw [this.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [p4m_inner_comm h' w, p4m_inner_comm h' h]
  field_simp
  ring

theorem p4m_gauss_poly_bound {v : ℝ} (hv : 0 < v) (m : ℕ) :
    ∀ w : EucConfig d N, p4m_q w ^ m * Real.exp (-(p4m_q w) / (2 * v)) ≤ (m.factorial : ℝ) * (2 * v) ^ m := by
  intro w
  have hq := p4m_q_nonneg w
  have h1 := Real.pow_div_factorial_le_exp (p4m_q w / (2 * v)) (by positivity) m
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have h2 : 0 < Real.exp (-(p4m_q w) / (2 * v)) := Real.exp_pos _
  have e : Real.exp (-(p4m_q w) / (2 * v)) * Real.exp (p4m_q w / (2 * v)) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  have h3 : (p4m_q w / (2 * v)) ^ m / m.factorial * Real.exp (-(p4m_q w) / (2 * v)) ≤ 1 := by
    calc _ ≤ Real.exp (p4m_q w / (2 * v)) * Real.exp (-(p4m_q w) / (2 * v)) :=
          mul_le_mul_of_nonneg_right h1 h2.le
      _ = 1 := by rw [mul_comm]; exact e
  have h4 : p4m_q w ^ m * Real.exp (-(p4m_q w) / (2 * v)) =
      (2 * v) ^ m * m.factorial *
        ((p4m_q w / (2 * v)) ^ m / m.factorial * Real.exp (-(p4m_q w) / (2 * v))) := by
    rw [div_pow]
    field_simp
  rw [h4]
  have : 0 ≤ (2 * v) ^ m * (m.factorial : ℝ) := by positivity
  calc _ ≤ (2 * v) ^ m * m.factorial * 1 := mul_le_mul_of_nonneg_left h3 this
    _ = _ := by ring

theorem p4m_gauss_poly_bound' {v : ℝ} (hv : 0 < v) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EucConfig d N, p4m_q w ^ m * p4Gauss d N v w ≤ C := by
  refine ⟨p4m_cst d N v * ((m.factorial : ℝ) * (2 * v) ^ m), by
    have := p4m_cst_pos (d := d) (N := N) hv; positivity, fun w => ?_⟩
  rw [p4m_gauss_eq]
  calc p4m_q w ^ m * (p4m_cst d N v * Real.exp (-(p4m_q w) / (2 * v)))
      = p4m_cst d N v * (p4m_q w ^ m * Real.exp (-(p4m_q w) / (2 * v))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (p4m_gauss_poly_bound hv m w) (p4m_cst_pos hv).le

end HRS.MP.SelfSimP4Mol
