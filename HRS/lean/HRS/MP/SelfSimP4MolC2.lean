import HRS.MP.SelfSimP4MolC1

/-!
# MPP4MOL stage 5b (2): integration by parts against the Gaussian
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_cont_deriv_coord {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (k : Fin N × Fin d) :
    Continuous (fun x => fderiv ℝ f x (configBasis d N k)) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem p4m_cs_deriv_coord {f : EucConfig d N → ℝ} (hfs : HasCompactSupport f) (k : Fin N × Fin d) :
    HasCompactSupport (fun x => fderiv ℝ f x (configBasis d N k)) :=
  hfs.fderiv_apply (𝕜 := ℝ) (configBasis d N k)

/-- Integration by parts in the direction `e_k` against a `C¹` function. -/
theorem p4m_ibp_cs {f g : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (hg : ContDiff ℝ 1 g) (k : Fin N × Fin d) :
    ∫ x, f x * fderiv ℝ g x (configBasis d N k) = -∫ x, fderiv ℝ f x (configBasis d N k) * g x := by
  have h1 : Integrable (fun x => fderiv ℝ f x (configBasis d N k) * g x) volume :=
    ((p4m_cont_deriv_coord hf k).mul hg.continuous).integrable_of_hasCompactSupport
      ((p4m_cs_deriv_coord hfs k).mul_right)
  have h2 : Integrable (fun x => f x * fderiv ℝ g x (configBasis d N k)) volume :=
    (hf.continuous.mul (p4m_cont_deriv_coord hg k)).integrable_of_hasCompactSupport hfs.mul_right
  have h3 : Integrable (fun x => f x * g x) volume :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfs.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (hf.differentiable (by norm_num)) x) (fun x _ => (hg.differentiable (by norm_num)) x)

section
variable {v : ℝ}

/-- The shifted Gaussian `x ↦ G(x - y)` is `C^∞`. -/
theorem p4m_contDiff_gauss_sub (v : ℝ) (y : EucConfig d N) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : EucConfig d N => p4Gauss d N v (x - y)) :=
  (p4m_contDiff_gauss v).comp (contDiff_id.sub contDiff_const)

theorem p4m_hasFDerivAt_gauss_sub (hv : 0 < v) (x y : EucConfig d N) :
    HasFDerivAt (fun x : EucConfig d N => p4Gauss d N v (x - y))
      ((-(1 / v) * p4Gauss d N v (x - y)) • p4InnerL (x - y)) x := by
  have h2 := (p4m_hasFDerivAt_gauss hv (x - y)).comp x ((hasFDerivAt_id x).sub_const y)
  rw [ContinuousLinearMap.comp_id] at h2
  exact h2

theorem p4m_fderiv_gauss_sub_basis (hv : 0 < v) (x y : EucConfig d N) (k : Fin N × Fin d) :
    fderiv ℝ (fun x : EucConfig d N => p4Gauss d N v (x - y)) x (configBasis d N k) =
      -(1 / v) * p4Gauss d N v (x - y) * (x - y) k.1 k.2 := by
  rw [(p4m_hasFDerivAt_gauss_sub hv x y).fderiv]
  simp [p4m_inner_single]

/-- The first derivative along `e_k` of the shifted Gaussian, as a function. -/
def p4m_gk (v : ℝ) (y : EucConfig d N) (k : Fin N × Fin d) (x : EucConfig d N) : ℝ :=
  -(1 / v) * p4Gauss d N v (x - y) * (x - y) k.1 k.2

theorem p4m_contDiff_gk (v : ℝ) (y : EucConfig d N) (k : Fin N × Fin d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (p4m_gk v y k) := by
  unfold p4m_gk
  refine (contDiff_const.mul (p4m_contDiff_gauss_sub v y)).mul ?_
  have : (fun x : EucConfig d N => (x - y) k.1 k.2) = fun x => p4InnerL (configBasis d N k) (x - y) := by
    funext x; rw [p4m_inner_single_left]
  rw [this]
  exact (p4InnerL (configBasis d N k)).contDiff.comp (contDiff_id.sub contDiff_const)

theorem p4m_fderiv_gk_basis (hv : 0 < v) (x y : EucConfig d N) (k : Fin N × Fin d) :
    fderiv ℝ (p4m_gk v y k) x (configBasis d N k) =
      ((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y) := by
  have hc : HasFDerivAt (fun x : EucConfig d N => p4InnerL (configBasis d N k) (x - y))
      (p4InnerL (configBasis d N k)) x := by
    have := (p4InnerL (configBasis d N k)).hasFDerivAt (x := x - y) |>.comp x ((hasFDerivAt_id x).sub_const y)
    rw [ContinuousLinearMap.comp_id] at this
    exact this
  have h := ((p4m_hasFDerivAt_gauss_sub hv x y).const_mul (-(1 / v))).fun_mul hc
  have e : p4m_gk v y k = fun x => -(1 / v) * p4Gauss d N v (x - y) * p4InnerL (configBasis d N k) (x - y) := by
    funext x; unfold p4m_gk; rw [p4m_inner_single_left]
  rw [e, h.fderiv]
  have hb1 : configBasis d N k k.1 k.2 = 1 := by simp [p4m_basis_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    p4m_inner_single, p4m_inner_single_left, hb1]
  field_simp
  ring

theorem p4m_ibp_gauss1 (hv : 0 < v) {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (y : EucConfig d N) (k : Fin N × Fin d) :
    ∫ x, f x * p4m_gk v y k x = -∫ x, fderiv ℝ f x (configBasis d N k) * p4Gauss d N v (x - y) := by
  have := p4m_ibp_cs hf hfs (p4m_contDiff_gauss_sub (n := 1) v y) k
  simp only [p4m_fderiv_gauss_sub_basis hv] at this
  exact this

theorem p4m_ibp_gauss2 (hv : 0 < v) {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f)
    (y : EucConfig d N) (k : Fin N × Fin d) :
    ∫ x, f x * (((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y)) =
      -∫ x, fderiv ℝ f x (configBasis d N k) * p4m_gk v y k x := by
  have := p4m_ibp_cs hf hfs (p4m_contDiff_gk (n := 1) v y k) k
  simp only [p4m_fderiv_gk_basis hv] at this
  exact this

end

end HRS.MP.SelfSimP4Mol
