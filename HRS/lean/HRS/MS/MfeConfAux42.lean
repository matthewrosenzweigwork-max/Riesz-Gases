import HRS.MS.MfeConfAux41

/-!
# S.B.1, packet F6 (part 4): the fixed-time inequality

`sb1_fixed_time`: for the mollified law `u = G_v * ν` and a cut-off `χ`,
`∫ χ a Λ ≤ ∫ χ u (-div w - ⟨w,b⟩/θ + |w|²/θ) + N Kl² (N d v)/(4θ) - ∑_k ∫ u w_k ∂_kχ - ∑_k ∫ Λ ∂_kχ J_k`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_fixed_time [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ : ℝ} (hθ : 0 < θ)
    {b : EucConfig d N → EucConfig d N} {Kl : ℝ≥0} (hbl : LipschitzWith Kl b) {B K : ℝ} (hB : 0 ≤ B)
    (hK : 0 ≤ K) (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) {H Ψ : EucConfig d N → ℝ} {w : EucConfig d N → EucConfig d N}
    (hH : ∀ x, HasFDerivAt H (-(p4InnerL (b x))) x) (hΨ : ∀ x, HasFDerivAt Ψ (p4InnerL (w x)) x)
    (hw : ContDiff ℝ 1 w) {χ : EucConfig d N → ℝ} (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) :
    ∫ x, χ x * (p4m_a v θ ν b x * p4m_Lam v θ ν (fun x => H x + Ψ x) x) ≤
      (∫ x, χ x * (p4Mol v ν x * (-(sb1div w x) - p4InnerL (w x) (b x) / θ + p4m_q (w x) / θ))) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ) -
        (∑ k : Fin N × Fin d, ∫ x, p4Mol v ν x * (w x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) -
        ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ ν (fun x => H x + Ψ x) x * fderiv ℝ χ x (configBasis d N k) *
          (θ * p4m_gu v ν k x - p4m_B v ν b k x) := by
  have hbc : Continuous b := hbl.continuous
  have hwc := hw.continuous
  have hHd : ContDiff ℝ 1 H := p4m_contDiff_V hbc hH
  have hΨd : ContDiff ℝ 1 Ψ := sb1_contDiff_of_grad hwc hΨ
  have hVd : ContDiff ℝ 1 (fun x => H x + Ψ x) := hHd.add hΨd
  have hΛ := p4m_contDiff_Lam hv hm θ hVd
  have hΛc : Continuous (p4m_Lam v θ ν (fun x => H x + Ψ x)) := hΛ.continuous
  have hf : ContDiff ℝ 1 (fun x => χ x * p4m_Lam v θ ν (fun x => H x + Ψ x) x) := hχ.mul hΛ
  have hfs : HasCompactSupport (fun x => χ x * p4m_Lam v θ ν (fun x => H x + Ψ x) x) := hχs.mul_right
  have ibp := p4m_ibp_identity hv θ hm hbc hB hK hbg hf hfs
  have hu := p4m_cont_u hv hm (ν := ν)
  have hgu := fun k => p4m_cont_gu hv hm (ν := ν) k
  have hBc := fun k => p4m_cont_B hv hm hbc hB hK hbg k
  have hellc : ∀ k : Fin N × Fin d, Continuous (fun x => p4m_ell v θ ν b k x + w x k.1 k.2 / θ) := by
    intro k
    have h1 : Continuous (p4m_ell v θ ν b k) := by
      unfold p4m_ell
      refine ((hgu k).div hu fun x => (p4m_mol_pos hv hm x).ne').sub ?_
      exact ((p4m_continuous_coord k).comp hbc).div_const θ
    exact h1.add (((p4m_continuous_coord k).comp hwc).div_const θ)
  have hJc : ∀ k : Fin N × Fin d, Continuous (fun x => θ * p4m_gu v ν k x - p4m_B v ν b k x) :=
    fun k => (continuous_const.mul (hgu k)).sub (hBc k)
  have hdχ : ∀ k : Fin N × Fin d, Continuous (fun x => fderiv ℝ χ x (configBasis d N k)) := fun k =>
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχs : ∀ k : Fin N × Fin d, HasCompactSupport (fun x => fderiv ℝ χ x (configBasis d N k)) :=
    fun k => hχs.fderiv_apply ℝ _
  -- derivative of the product
  have hfd : ∀ (k : Fin N × Fin d) x,
      fderiv ℝ (fun x => χ x * p4m_Lam v θ ν (fun x => H x + Ψ x) x) x (configBasis d N k) =
      χ x * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) +
        p4m_Lam v θ ν (fun x => H x + Ψ x) x * fderiv ℝ χ x (configBasis d N k) := by
    intro k x
    have h1 := (hχ.differentiable (by norm_num) x).hasFDerivAt
    have h2 := (hΛ.differentiable (by norm_num) x).hasFDerivAt
    rw [(h1.fun_mul h2).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [sb1_fderiv_Lam_gen hv hm θ hH hΨ k x]
  simp_rw [hfd, add_mul] at ibp
  have hi1 : ∀ k : Fin N × Fin d, Integrable (fun x => χ x * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) *
      (θ * p4m_gu v ν k x - p4m_B v ν b k x)) := fun k =>
    p4m_int_of_supp (((hχ.continuous.mul (hellc k)).mul (hJc k))) hχs fun x h => by simp [h]
  have hi2 : ∀ k : Fin N × Fin d, Integrable (fun x => p4m_Lam v θ ν (fun x => H x + Ψ x) x *
      fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v ν k x - p4m_B v ν b k x)) := fun k =>
    p4m_int_of_supp (((hΛc.mul (hdχ k)).mul (hJc k))) (hdχs k) fun x h => by simp [h]
  simp_rw [integral_add (hi1 _) (hi2 _)] at ibp
  rw [Finset.sum_add_distrib] at ibp
  have hQ := p4m_Q_integrable hv (ν := ν)
  have hiA : Integrable fun x => -∑ k : Fin N × Fin d, χ x * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) *
      (θ * p4m_gu v ν k x - p4m_B v ν b k x) := (integrable_finset_sum _ fun k _ => hi1 k).neg
  have key : ∫ x, χ x * (p4m_a v θ ν b x * p4m_Lam v θ ν (fun x => H x + Ψ x) x) =
      (∫ x, -∑ k : Fin N × Fin d, χ x * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ ν (fun x => H x + Ψ x) x * fderiv ℝ χ x (configBasis d N k) *
          (θ * p4m_gu v ν k x - p4m_B v ν b k x) := by
    rw [integral_neg, integral_finset_sum _ fun k _ => hi1 k]
    have e : ∫ x, χ x * (p4m_a v θ ν b x * p4m_Lam v θ ν (fun x => H x + Ψ x) x) =
        ∫ x, χ x * p4m_Lam v θ ν (fun x => H x + Ψ x) x * p4m_a v θ ν b x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [e, ibp]
    ring
  rw [key]
  -- the cross term
  have hcross := sb1_ibp_w hv hm hθ hbc hw hχ hχs (b := b)
  have hcont : Continuous fun x => χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 *
      (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) :=
    hχ.continuous.mul (hu.mul (continuous_finset_sum _ fun k _ =>
      ((p4m_continuous_coord k).comp hwc).mul (hellc k)))
  have hiu : Integrable fun x => χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 *
      (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) :=
    p4m_int_of_supp hcont hχs fun x h => by simp [h]
  have hmain : (∫ x, -∑ k : Fin N × Fin d, χ x * (p4m_ell v θ ν b k x + w x k.1 k.2 / θ) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)) ≤
      (∫ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 *
        (p4m_ell v θ ν b k x + w x k.1 k.2 / θ))) + N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ) := by
    have hg : ((∫ x, χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 *
        (p4m_ell v θ ν b k x + w x k.1 k.2 / θ))) + N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) =
        ∫ x, (χ x * (p4Mol v ν x * ∑ k : Fin N × Fin d, w x k.1 k.2 *
          (p4m_ell v θ ν b k x + w x k.1 k.2 / θ)) + N * (Kl : ℝ) ^ 2 * p4m_Q v ν x / (4 * θ)) := by
      rw [integral_add hiu ((hQ.const_mul _).div_const _), integral_div, integral_const_mul, p4m_Q_integral hv]
    rw [hg]
    refine integral_mono hiA (hiu.add ((hQ.const_mul _).div_const _)) fun x => ?_
    exact sb1_pointwise hv hm hθ hbl hB hK hbg x (hχ0 x) (hχ1 x)
  rw [hcross] at hmain
  linarith

end

end HRS.MS.MfeConf
