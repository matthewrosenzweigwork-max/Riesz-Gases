import HRS.MS.S82RA3

/-!
# S8.2 R01A (S82R), part 4: the rate `O(delta_N)` of the calibrated field
`|<t_N, Xi(x)>| <= 4 beta k(0) ||theta_N - 1||_{L^1(mu)}`, from `t_N = -beta Xibar` and `int Xi dmu = 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wr HRS.MS.Psd

variable {d : ℕ}

namespace S82RCtx

variable {a beta : ℝ} {rho : Euc d → ℝ} {M tau CR : ℝ} {N0 : ℕ}

theorem field_rate (c : S82RCtx d a beta rho M tau CR N0) {N : ℕ} (hN : N0 ≤ N) (x : Euc d) :
    |s82r_field d rho beta tau N0 N x| ≤
      4 * beta * kTau d (criticalS d) tau 0 * (CR * HRS.MS.Phase2S82.deltaN N) := by
  haveI := c.prob
  have hN1 : 0 < N := by have := c.hN0; omega
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [c.field_of_le hN x]
  have hsd := s82r_criticalS_pos c.hd1
  set k0 := kTau d (criticalS d) tau 0 with hk0
  have hk0n : 0 ≤ k0 := kTau_nonneg hsd c.htau 0
  have hcal := c.calfeat
  have hsq : Real.sqrt k0 * Real.sqrt k0 = k0 := Real.mul_self_sqrt hk0n
  obtain ⟨hac, hL2⟩ := c.hL2 (n + 1) hN
  set dq : Euc d → Euc d → ℝ := fun x y : Euc d => qTau d (criticalS d) tau (x - y) with hdq
  set μ := HRS.Whole.withDensityReal rho with hμ
  set Ψ := featMap d (criticalS d) tau with hΨ
  haveI hRNp : IsProbabilityMeasure (RN dq μ Ψ beta (n + 1)) :=
    wr11b_isProb_RN c.trans c.hbeta.le hN1
  set m := HRS.Whole.firstMarginal (RN dq μ Ψ beta (n + 1)) with hm
  haveI hmp : IsProbabilityMeasure m := wr14a_isProb_firstMarginal hN1 (RN dq μ Ψ beta (n + 1))
  haveI : m.HaveLebesgueDecomposition μ := Measure.haveLebesgueDecomposition_of_sigmaFinite m μ
  have ht1 := c.hfs (n + 1) hN
  have hXi := wr13e_Xibar_eq_integral c.weak c.ha c.hbeta c.calfeat (n := n) ht1
  have hteq := tN_eq c.weak c.calfeat c.hbeta hN1
  set f : Euc d → ℝ := fun y => (m.rnDeriv μ y).toReal with hf
  have hfi : Integrable f μ := Measure.integrable_toReal_rnDeriv
  set G : Euc d → ℝ := fun y => inner ℝ (Xi μ Ψ x) (Xi μ Ψ y) with hG
  have hGc : Continuous G := continuous_const.inner c.calfeat.continuous_Xi
  have hGb : ∀ y, |G y| ≤ 4 * k0 := by
    intro y
    have h1 : |G y| ≤ ‖Xi μ Ψ x‖ * ‖Xi μ Ψ y‖ := abs_real_inner_le_norm _ _
    refine h1.trans ?_
    have := mul_le_mul (hcal.norm_Xi_le (μ := μ) x) (hcal.norm_Xi_le (μ := μ) y) (norm_nonneg _) (by positivity)
    calc ‖Xi μ Ψ x‖ * ‖Xi μ Ψ y‖ ≤ 2 * Real.sqrt k0 * (2 * Real.sqrt k0) := this
      _ = 4 * k0 := by nlinarith [hsq]
  have hGi : Integrable G μ :=
    Integrable.of_bound hGc.aestronglyMeasurable (4 * k0)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hGb y)
  have hfGi : Integrable (fun y => G y * f y) μ :=
    Integrable.bdd_mul (c := 4 * k0) hfi hGc.aestronglyMeasurable
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hGb y)
  have hXint : Integrable (Xi μ Ψ) m := by
    refine Integrable.of_bound hcal.continuous_Xi.aestronglyMeasurable (2 * Real.sqrt k0)
      (ae_of_all _ fun y => hcal.norm_Xi_le y)
  -- inner(Xibar, Xi x) as an integral
  have hinner : inner ℝ (Xibar dq μ Ψ beta (n + 1)) (Xi μ Ψ x) = ∫ y, G y * f y ∂μ := by
    rw [hXi, real_inner_comm, ← integral_inner hXint (Xi μ Ψ x)]
    have := integral_toReal_rnDeriv_mul (μ := m) (ν := μ) hac (f := G)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hf]
    ring
  have hcenter : ∫ y, G y ∂μ = 0 := wr12b_integral_inner_Xi c.calfeat (Xi μ Ψ x)
  have hsplit : ∫ y, G y * f y ∂μ = ∫ y, G y * (f y - 1) ∂μ := by
    have h1 : ∫ y, G y * (f y - 1) ∂μ = ∫ y, G y * f y ∂μ - ∫ y, G y ∂μ := by
      rw [← integral_sub hfGi hGi]
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      ring
    rw [h1, hcenter, sub_zero]
  -- L1 bound
  have hf1 : Integrable (fun y => f y - 1) μ := hfi.sub (integrable_const 1)
  have hL1 : ∫ y, |f y - 1| ∂μ ≤ CR * HRS.MS.Phase2S82.deltaN (n + 1) := by
    have h2 : eLpNorm (fun y => f y - 1) 2 μ ≤
        ENNReal.ofReal (CR * HRS.MS.Phase2S82.deltaN (n + 1)) := by
      rw [← s82r_deltaN_eq d (n + 1)]; exact hL2
    have h1 : eLpNorm (fun y => f y - 1) 1 μ ≤ eLpNorm (fun y => f y - 1) 2 μ :=
      eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
    rw [eLpNorm_one_eq_lintegral_enorm hf1.aestronglyMeasurable] at h1
    have h3 : ENNReal.ofReal (∫ y, ‖f y - 1‖ ∂μ) ≤
        ENNReal.ofReal (CR * HRS.MS.Phase2S82.deltaN (n + 1)) := by
      rw [ofReal_integral_norm_eq_lintegral_enorm hf1]
      exact h1.trans h2
    have hδ : 0 ≤ CR * HRS.MS.Phase2S82.deltaN (n + 1) :=
      mul_nonneg c.hCR (s82r_deltaN_nonneg hN1)
    have := (ENNReal.ofReal_le_ofReal_iff hδ).1 h3
    simpa [Real.norm_eq_abs] using this
  have hbd : |∫ y, G y * (f y - 1) ∂μ| ≤ 4 * k0 * ∫ y, |f y - 1| ∂μ := by
    calc |∫ y, G y * (f y - 1) ∂μ| = ‖∫ y, G y * (f y - 1) ∂μ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖G y * (f y - 1)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, 4 * k0 * |f y - 1| ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
            (hf1.abs.const_mul _) (ae_of_all _ fun y => ?_)
          show ‖G y * (f y - 1)‖ ≤ 4 * k0 * |f y - 1|
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul (hGb y) le_rfl (abs_nonneg _) (by positivity)
      _ = 4 * k0 * ∫ y, |f y - 1| ∂μ := integral_const_mul _ _
  rw [hteq, real_inner_smul_left, hinner, hsplit]
  rw [abs_mul, abs_neg, abs_of_pos c.hbeta]
  calc beta * |∫ y, G y * (f y - 1) ∂μ| ≤ beta * (4 * k0 * ∫ y, |f y - 1| ∂μ) :=
        mul_le_mul_of_nonneg_left hbd c.hbeta.le
    _ ≤ beta * (4 * k0 * (CR * HRS.MS.Phase2S82.deltaN (n + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL1 (by positivity)) c.hbeta.le
    _ = 4 * beta * k0 * (CR * HRS.MS.Phase2S82.deltaN (n + 1)) := by ring

end S82RCtx

end HRS.MS.S82R

end
