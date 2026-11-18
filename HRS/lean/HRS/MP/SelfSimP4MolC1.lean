import HRS.MP.SelfSimP4MolB4

/-!
# MPP4MOL stage 5b (1): the functions `∂_k u`, `B_k`, `a` attached to a law `ν` and a drift `b`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- `∂_k u (x) = ∫ -(1/v) G(x-y) (x-y)_k dν(y)`. -/
def p4m_gu (v : ℝ) (ν : Measure (EucConfig d N)) (k : Fin N × Fin d) (x : EucConfig d N) : ℝ :=
  ∫ y, (-(1 / v) * p4Gauss d N v (x - y) * (x - y) k.1 k.2) ∂ν

/-- `B_k(x) = ∫ G(x-y) b_k(y) dν(y)`. -/
def p4m_B (v : ℝ) (ν : Measure (EucConfig d N)) (b : EucConfig d N → EucConfig d N) (k : Fin N × Fin d)
    (x : EucConfig d N) : ℝ :=
  ∫ y, p4Gauss d N v (x - y) * b y k.1 k.2 ∂ν

/-- The integrand of the time derivative of `u`. -/
def p4m_ha (v θ : ℝ) (b : EucConfig d N → EucConfig d N) (x y : EucConfig d N) : ℝ :=
  p4Gauss d N v (x - y) *
    (θ * (p4m_q (x - y) / v ^ 2 - ((N * d : ℕ) : ℝ) / v) + p4InnerL (x - y) (b y) / v)

/-- `a(x) = ∫ ha(x,y) dν(y)`. -/
def p4m_a (v θ : ℝ) (ν : Measure (EucConfig d N)) (b : EucConfig d N → EucConfig d N)
    (x : EucConfig d N) : ℝ :=
  ∫ y, p4m_ha v θ b x y ∂ν

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_integrable_lin [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {φ : EucConfig d N → ℝ}
    (hφ : AEStronglyMeasurable φ ν) {A : ℝ} (hb : ∀ y, |φ y| ≤ A * (1 + ‖y‖)) : Integrable φ ν := by
  have : Integrable (fun y => A * (2 + p4m_q y)) ν := ((integrable_const 2).add hm).const_mul A
  refine this.mono' hφ (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (hb y).trans ?_
  have h1 := p4m_norm_le_q_add y
  have hA : 0 ≤ A := by
    have := (abs_nonneg (φ 0)).trans (hb 0)
    simp only [norm_zero, add_zero, mul_one] at this
    exact this
  nlinarith

theorem p4m_fderiv_mol_basis (hv : 0 < v) [IsProbabilityMeasure ν] (k : Fin N × Fin d) (x : EucConfig d N) :
    fderiv ℝ (p4Mol v ν) x (configBasis d N k) = p4m_gu v ν k x := by
  rw [p4m_fderiv_mol_apply hv]
  unfold p4m_gu
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [p4m_inner_single]

/-- Product integrability of `F(x) φ(x,y)` for compactly supported continuous `F`. -/
theorem p4m_prod_integrable_cs [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {F : EucConfig d N → ℝ} (hF : Continuous F) (hFs : HasCompactSupport F)
    {φ : EucConfig d N → EucConfig d N → ℝ} (hφc : Continuous (fun p : EucConfig d N × EucConfig d N => φ p.1 p.2))
    {A : ℝ} (hφ : ∀ x y, |φ x y| ≤ A * (1 + ‖y‖)) :
    Integrable (fun p : EucConfig d N × EucConfig d N => F p.1 * φ p.1 p.2)
      ((volume : Measure (EucConfig d N)).prod ν) := by
  have hFi : Integrable F volume := hF.integrable_of_hasCompactSupport hFs
  have hmi : Integrable (fun y : EucConfig d N => A * (1 + ‖y‖)) ν := by
    have hA : 0 ≤ A := by
      have := (abs_nonneg (φ 0 0)).trans (hφ 0 0)
      simp only [norm_zero, add_zero, mul_one] at this
      exact this
    refine (((integrable_const 2).add hm).const_mul A).mono' (continuous_const.mul
      (continuous_const.add continuous_norm)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := p4m_norm_le_q_add y
    show A * (1 + ‖y‖) ≤ A * (2 + p4m_q y)
    nlinarith
  have h1 := hFi.norm.mul_prod hmi
  refine h1.mono' ((hF.comp continuous_fst).mul hφc).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hφ _ _) (abs_nonneg _) |>.trans (by simp)

end

end HRS.MP.SelfSimP4Mol
