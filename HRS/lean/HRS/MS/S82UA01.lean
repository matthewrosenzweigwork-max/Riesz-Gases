import HRS.MS.S82UE1

/-!
# S8.2 A01 (frozen statement of the Pro skeleton `S82.A01`): canonical triple and repeated-pair bounds
Route: measurable symmetric model `uG` of the grouped triple kernel (edge grouping, gradient bound by a Hessian
mean value on a ball or by the two separate gradient bounds), zero `μ`-row from the Jmean identity
`∫ ρ J ψ = -∫ ρ <ψ, F_μ>` (truncation `|x-z| > ε` and antisymmetry).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

theorem canonical_triple_and_bounds (d : ℕ) (hd : 2 ≤ d)
    (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) :
    ∃ C M' : ℝ, 0 ≤ C ∧ 0 ≤ M' ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M A f Q →
      ∃ G : Euc d → Euc d → Euc d → ℝ,
        Measurable (fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2) ∧
        CanonicalTriple (HRS.Whole.withDensityReal rho) G ∧
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z →
          G x y z = tripleG (critCoeff d a beta rho) rho Q x y z ∧
          |G x y z| ≤ C * A * jbracket x ^ M' * jbracket y ^ M' *
            jbracket z ^ M' * triplePole x y z) ∧
        ∀ x y, x ≠ y →
          |repeatedB rho Q x y| ≤ C * A * pairWeight M' x y * pole x y ^ 2 := by
  obtain ⟨Λ0, Gc0, c0, K, hF0, hρG0, hG0, hc0, hK0, hFm0, hK⟩ := HRS.MS.S82U.u_thermal hd ha hbeta
  set Ce := HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) with hCe
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hσ := HRS.MS.S82T.s82t_sigma_nonneg (criticalS d) hs0
  have hCe0 : 0 ≤ Ce := mul_nonneg hσ (by positivity)
  refine ⟨(Ce + 2 * K + 1) + (2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * K), 2 * M,
    by positivity, by linarith, ?_⟩
  intro rho hrho f A hA Q hQ
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  set rho := HRS.Whole.thermalDensity d (criticalS d) a beta with hrhodef
  set mu := HRS.Whole.withDensityReal rho with hmu
  haveI : IsProbabilityMeasure mu := HRS.Whole.Q09A.measure_isProb hF0.prob
  set Fm := forceMean rho with hFm
  set g := HRS.MS.S82P2.s82p2_gt Q with hg
  set C0 := critCoeff d a beta rho with hC0
  set Jt := HRS.MS.S82T.s82t_Jt C0 mu g with hJt
  have hJsymm : ∀ x y, Jt x y = Jt y x := fun x y => HRS.MS.S82T.s82t_Jt_symm C0 mu g x y
  have hρm : Measurable (C0.ρ 0) := hF0.prob.measurable
  have hJm : Measurable (Function.uncurry Jt) :=
    HRS.MS.S82T.s82t_Jt_measurable C0 mu hρm (HRS.MS.S82P2.s82p2_gt_measurable Q)
  have hgm : Measurable (Function.uncurry g) := HRS.MS.S82P2.s82p2_gt_measurable Q
  have hGm : Measurable (rieszKernelGrad d (criticalS d)) :=
    HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hJsmall : ∀ p q : Euc d, p ≠ q → |Jt p q| ≤ A * Phase2S82.pairWeight M p q * pole p q :=
    fun p q hpq => HRS.MS.S82U.u_hJsmall hd hQ p q hpq
  refine ⟨HRS.MS.S82U.uG Fm g Jt, HRS.MS.S82U.u_uG_meas hFm0 hgm hJm,
    ⟨fun x y z => HRS.MS.S82U.uG_symm Fm g Jt hJsymm x y z, ?_⟩, ?_, ?_⟩
  · -- integrability and zero row
    intro x y hxy
    have hae : ∀ᵐ z ∂mu, HRS.MS.S82U.uG Fm g Jt x y z = HRS.MS.S82U.uGm Fm g Jt x y z := by
      filter_upwards [HRS.MS.S82T.s82t_mu_ae_ne hd rho x, HRS.MS.S82T.s82t_mu_ae_ne hd rho y] with z hzx hzy
      unfold HRS.MS.S82U.uG
      rw [if_pos ⟨hxy, hzx.symm, hzy.symm⟩]
    have hint := HRS.MS.S82U.u_int_triple hd (by linarith : 0 ≤ 2 * M) hG0.le hc0 hF0.prob hρG0 hxy
    have hb := hint.const_mul ((Ce + 2 * K + 1) * (A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M))))
    have hbound : ∀ᵐ z ∂mu, ‖HRS.MS.S82U.uGm Fm g Jt x y z‖ ≤
        ((Ce + 2 * K + 1) * (A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M)))) *
          (jbracket z ^ (2 * M) * triplePole x y z) := by
      filter_upwards [HRS.MS.S82T.s82t_mu_ae_ne hd rho x, HRS.MS.S82T.s82t_mu_ae_ne hd rho y] with z hzx hzy
      rw [Real.norm_eq_abs]
      have := HRS.MS.S82U.uGm_bound hd hM hA hQ hK0 hK hJsmall hxy hzx.symm hzy.symm
      refine this.trans (le_of_eq ?_)
      unfold HRS.MS.S82U.uW
      ring
    have hI : Integrable (fun z => HRS.MS.S82U.uGm Fm g Jt x y z) mu :=
      Integrable.mono' hb (HRS.MS.S82U.u_uGm_sec_meas hFm0 hgm hJm x y).aestronglyMeasurable hbound
    refine ⟨hI.congr (hae.mono fun z hz => hz.symm), ?_⟩
    rw [integral_congr_ae hae]
    exact HRS.MS.S82U.u_zero_row hd hM hA hQ hF0 hG0 hc0 hρG0 hFm0 hK hxy
  · -- pointwise statements
    intro x y z hxy hxz hyz
    have hdist : x ≠ y ∧ x ≠ z ∧ y ≠ z := ⟨hxy, hxz, hyz⟩
    have hG : HRS.MS.S82U.uG Fm g Jt x y z = HRS.MS.S82U.uGm Fm g Jt x y z := by
      unfold HRS.MS.S82U.uG; rw [if_pos hdist]
    have htg := HRS.MS.S82U.u_tripleG_eq hd hQ hxy hxz hyz
    refine ⟨by rw [hG]; exact htg.symm, ?_⟩
    rw [hG]
    have := HRS.MS.S82U.uGm_bound hd hM hA hQ hK0 hK hJsmall hxy hxz hyz
    refine this.trans ?_
    unfold HRS.MS.S82U.uW
    have hX : 0 ≤ A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M) * jbracket z ^ (2 * M)) *
        triplePole x y z := by
      have := HRS.MS.S82U.u_tp_ge x y z
      refine mul_nonneg (mul_nonneg hA (mul_nonneg (mul_nonneg (HRS.MS.S82U.u_jb_rpow_pos _ _).le
        (HRS.MS.S82U.u_jb_rpow_pos _ _).le) (HRS.MS.S82U.u_jb_rpow_pos _ _).le)) ?_
      linarith [this.1, HRS.MS.S82U.u_pole_pos x y]
    have e : (Ce + 2 * K + 1 + (2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * K)) * A *
        jbracket x ^ (2 * M) * jbracket y ^ (2 * M) * jbracket z ^ (2 * M) * triplePole x y z =
        (Ce + 2 * K + 1 + (2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * K)) *
          (A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M) * jbracket z ^ (2 * M)) * triplePole x y z) := by
      ring
    rw [e]
    have hc : 0 ≤ 2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * K := by linarith
    nlinarith [mul_nonneg hc hX]
  · -- repeated B bound
    intro x y hxy
    rw [HRS.MS.S82T.s82t_repeatedB_eq hQ x y hxy]
    have hb := HRS.MS.S82T.s82t_B0_bound hd hQ hA hK0 hK x y hxy
    refine hb.trans ?_
    have hw : Phase2S82.pairWeight M x y ≤ Phase2S82.pairWeight (2 * M) x y := by
      unfold Phase2S82.pairWeight
      exact mul_le_mul (HRS.MS.S82U.u_jb_le_two hM x) (HRS.MS.S82U.u_jb_le_two hM y)
        (HRS.MS.S82U.u_jb_rpow_pos M y).le (HRS.MS.S82U.u_jb_rpow_pos _ x).le
    have hX : 0 ≤ A * Phase2S82.pairWeight (2 * M) x y * pole x y ^ 2 := by
      refine mul_nonneg (mul_nonneg hA ?_) (sq_nonneg _)
      unfold Phase2S82.pairWeight
      exact mul_nonneg (HRS.MS.S82U.u_jb_rpow_pos _ _).le (HRS.MS.S82U.u_jb_rpow_pos _ _).le
    have hle : A * Phase2S82.pairWeight M x y * pole x y ^ 2 ≤
        A * Phase2S82.pairWeight (2 * M) x y * pole x y ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hA) (sq_nonneg _)
    have hc : 0 ≤ 2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * K := by linarith
    have hc2 : 0 ≤ Ce + 2 * K + 1 := by linarith
    nlinarith [mul_nonneg hc hX, mul_le_mul_of_nonneg_left hle hc, mul_nonneg hc2 hX]

end HRS.MS.Phase2S82
