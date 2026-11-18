import HRS.MP.SelfSimP4MolD3

/-!
# MPP4MOL stage 5c (4): the fixed-time inequality for the cut-off Lambda-integral
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_int_of_supp {h g : EucConfig d N → ℝ} (hh : Continuous h) (hg : HasCompactSupport g)
    (hs : ∀ x, g x = 0 → h x = 0) : Integrable h := by
  refine hh.integrable_of_hasCompactSupport (hg.mono ?_)
  intro x hx
  by_contra hgx
  exact hx (hs x (not_not.1 hgx))

theorem p4m_T_nonneg (v : ℝ) (hv : 0 < v) (ν : Measure (EucConfig d N))
    (b : EucConfig d N → EucConfig d N) (x : EucConfig d N) : 0 ≤ p4m_T v ν b x :=
  integral_nonneg fun y => mul_nonneg (p4m_gauss_pos hv _).le (Finset.sum_nonneg fun k _ => sq_nonneg _)

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_fixed_time [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ δ : ℝ}
    (hθ : 0 < θ) (hδ : 0 < δ) {b : EucConfig d N → EucConfig d N} {Kl : ℝ≥0}
    (hbl : LipschitzWith Kl b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) {V : EucConfig d N → ℝ}
    (hV : ∀ x, HasFDerivAt V (-(p4InnerL (b x))) x) {χ : EucConfig d N → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) :
    ∫ x, χ x * (p4m_a v θ ν b x * p4m_Lam v θ ν V x) ≤
      -(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2)) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ) -
        ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) *
          (θ * p4m_gu v ν k x - p4m_B v ν b k x) := by
  have hbc : Continuous b := hbl.continuous
  have hΛ := p4m_contDiff_Lam hv hm θ (p4m_contDiff_V hbc hV)
  have hΛc : Continuous (p4m_Lam v θ ν V) := hΛ.continuous
  have hf : ContDiff ℝ 1 (fun x => χ x * p4m_Lam v θ ν V x) := hχ.mul hΛ
  have hfs : HasCompactSupport (fun x => χ x * p4m_Lam v θ ν V x) := hχs.mul_right
  have ibp := p4m_ibp_identity hv θ hm hbc hB hK hbg hf hfs
  have hu := p4m_cont_u hv hm (ν := ν)
  have hgu := fun k => p4m_cont_gu hv hm (ν := ν) k
  have hBc := fun k => p4m_cont_B hv hm hbc hB hK hbg k
  have hellc : ∀ k : Fin N × Fin d, Continuous (p4m_ell v θ ν b k) := by
    intro k
    unfold p4m_ell
    refine ((hgu k).div hu fun x => (p4m_mol_pos hv hm x).ne').sub ?_
    exact ((p4m_continuous_coord k).comp hbc).div_const θ
  have hJc : ∀ k : Fin N × Fin d, Continuous (fun x => θ * p4m_gu v ν k x - p4m_B v ν b k x) :=
    fun k => (continuous_const.mul (hgu k)).sub (hBc k)
  have hdχ : ∀ k : Fin N × Fin d, Continuous (fun x => fderiv ℝ χ x (configBasis d N k)) := fun k =>
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχs : ∀ k : Fin N × Fin d, HasCompactSupport (fun x => fderiv ℝ χ x (configBasis d N k)) :=
    fun k => hχs.fderiv_apply ℝ _
  -- derivative of the product
  have hfd : ∀ (k : Fin N × Fin d) x, fderiv ℝ (fun x => χ x * p4m_Lam v θ ν V x) x (configBasis d N k) =
      χ x * p4m_ell v θ ν b k x + p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) := by
    intro k x
    have h1 := (hχ.differentiable (by norm_num) x).hasFDerivAt
    have h2 := (hΛ.differentiable (by norm_num) x).hasFDerivAt
    rw [(h1.fun_mul h2).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [p4m_fderiv_Lam_basis hv hm θ hV k x]
  simp_rw [hfd, add_mul] at ibp
  have hi1 : ∀ k : Fin N × Fin d, Integrable (fun x => χ x * p4m_ell v θ ν b k x *
      (θ * p4m_gu v ν k x - p4m_B v ν b k x)) := fun k =>
    p4m_int_of_supp (((hχ.continuous.mul (hellc k)).mul (hJc k))) hχs fun x h => by simp [h]
  have hi2 : ∀ k : Fin N × Fin d, Integrable (fun x => p4m_Lam v θ ν V x *
      fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v ν k x - p4m_B v ν b k x)) := fun k =>
    p4m_int_of_supp (((hΛc.mul (hdχ k)).mul (hJc k))) (hdχs k) fun x h => by simp [h]
  simp_rw [integral_add (hi1 _) (hi2 _)] at ibp
  rw [Finset.sum_add_distrib] at ibp
  have hQ := p4m_Q_integrable hv (ν := ν)
  have hcu : Continuous fun x => χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2) :=
    hχ.continuous.mul (hu.mul (continuous_finset_sum _ fun k _ => (hellc k).pow 2))
  have hiu : Integrable fun x => χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2) :=
    p4m_int_of_supp hcu hχs fun x h => by simp [h]
  have hiA : Integrable fun x => -∑ k : Fin N × Fin d, χ x * p4m_ell v θ ν b k x *
      (θ * p4m_gu v ν k x - p4m_B v ν b k x) :=
    (integrable_finset_sum _ fun k _ => hi1 k).neg
  have key : ∫ x, χ x * (p4m_a v θ ν b x * p4m_Lam v θ ν V x) =
      (∫ x, -∑ k : Fin N × Fin d, χ x * p4m_ell v θ ν b k x *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) *
          (θ * p4m_gu v ν k x - p4m_B v ν b k x) := by
    rw [integral_neg, integral_finset_sum _ fun k _ => hi1 k]
    have e : ∫ x, χ x * (p4m_a v θ ν b x * p4m_Lam v θ ν V x) =
        ∫ x, χ x * p4m_Lam v θ ν V x * p4m_a v θ ν b x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [e, ibp]
    ring
  rw [key]
  have hmain : (∫ x, -∑ k : Fin N × Fin d, χ x * p4m_ell v θ ν b k x *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)) ≤
      -(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2)) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ) := by
    have hg : (-(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2)) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ)) =
        ∫ x, (-(θ * (1 - δ)) * (χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2)) +
          N * (Kl : ℝ) ^ 2 * p4m_Q v ν x / (4 * θ * δ)) := by
      rw [integral_add (hiu.const_mul _) ((hQ.const_mul _).div_const _), integral_const_mul,
        integral_div, integral_const_mul, p4m_Q_integral hv]
    rw [hg]
    refine integral_mono hiA ((hiu.const_mul _).add ((hQ.const_mul _).div_const _)) fun x => ?_
    simp only
    have hy := p4m_young_pt hv hm hθ hδ hbl hB hK hbg x
    have hTQ := p4m_T_le_Q hv hm hbl hB hK hbg x
    have hT0 := p4m_T_nonneg v hv ν b x
    have hχx0 := hχ0 x
    have hχx1 := hχ1 x
    have hJ : ∀ k : Fin N × Fin d, χ x * p4m_ell v θ ν b k x *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x) =
        χ x * (θ * p4Mol v ν x * p4m_ell v θ ν b k x ^ 2) -
          χ x * ((p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2) * p4m_ell v θ ν b k x) := by
      intro k
      rw [p4m_J_eq hv hm hθ b k x]
      ring
    simp_rw [hJ]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have hp4 : 0 < 4 * θ * δ := by positivity
    have h1 := mul_le_mul_of_nonneg_left hy hχx0
    have h2 : χ x * (p4m_T v ν b x / (4 * θ * δ)) ≤ p4m_T v ν b x / (4 * θ * δ) :=
      mul_le_of_le_one_left (div_nonneg hT0 hp4.le) hχx1
    have h3 : p4m_T v ν b x / (4 * θ * δ) ≤ N * (Kl : ℝ) ^ 2 * p4m_Q v ν x / (4 * θ * δ) :=
      div_le_div_of_nonneg_right hTQ hp4.le
    nlinarith
  linarith

end

end HRS.MP.SelfSimP4Mol
