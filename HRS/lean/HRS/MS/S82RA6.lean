import HRS.MS.S82RA5
import HRS.MS.CanThmAux1
import HRS.MS.QsfCorr2

/-!
# S8.2 R01A (S82R): `calibrated_reference_native` (frozen statement of the Pro skeleton `S82.R01A`)
Choice of the heat cutoff `tau`, the switch `N0`, the constants, and assembly of `CalibratedReferenceData`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Wr HRS.MS.Psd HRS.MS.Phase2S82

variable {d : ℕ}

/-- The heat cutoff can be chosen with `beta * a_tau <= 1/1000`. -/
lemma s82r_tau_exists (hs : 0 < criticalS d) (hsd : criticalS d < d) {beta : ℝ} (hbeta : 0 < beta)
    (M : ℝ) : ∃ tau : ℝ, 0 < tau ∧ beta * wr13e_a d (criticalS d) tau M ≤ 1 / 1000 := by
  set s := criticalS d with hsdef
  have hd0 : (0 : ℝ) < d := by linarith
  set α : ℝ := ((d : ℝ) - s) / 2 with hαdef
  have hα : 0 < α := by rw [hαdef]; linarith
  set ε : ℝ := 1 / 1000 with hε
  have hε0 : 0 < ε := by norm_num
  set X : ℝ := beta * max M 0 * wr12_cq d s with hX
  have hX0 : 0 ≤ X := by
    have := wr12_cq_nonneg (d := d) hs hsd
    rw [hX]; positivity
  obtain ⟨tau, htaudef⟩ : ∃ tau : ℝ, tau = (ε / (X + 1)) ^ (1 / α) := ⟨_, rfl⟩
  have htau : 0 < tau := by rw [htaudef]; exact Real.rpow_pos_of_pos (by positivity) _
  have htauα : tau ^ α = ε / (X + 1) := by
    rw [htaudef, ← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one]
  refine ⟨tau, htau, ?_⟩
  unfold wr13e_a
  rw [← hαdef]
  calc beta * (max M 0 * (wr12_cq d s * tau ^ α)) = X * tau ^ α := by rw [hX]; ring
    _ = X * (ε / (X + 1)) := by rw [htauα]
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith

lemma s82r_delta_ge {N : ℕ} (hN : 1 ≤ N) : 1 / (N : ℝ) ≤ HRS.MS.Phase2S82.deltaN N := by
  unfold HRS.MS.Phase2S82.deltaN HRS.MS.Phase2S82.logN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine div_le_div_of_nonneg_right ?_ hN0.le
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : 1 ≤ Real.exp 1 * N := by
    have := Real.one_le_exp (x := 1) (by norm_num)
    nlinarith
  have h3 : Real.log (Real.exp 1 * N) = 1 + Real.log N := by
    rw [Real.log_mul (Real.exp_pos _).ne' hN0.ne', Real.log_exp]
  rw [h3]
  have := Real.log_nonneg h1
  linarith

end HRS.MS.S82R

namespace HRS.MS.Phase2S82
open HRS HRS.Whole HRS.MS.Wr HRS.MS.Psd

/-- R01A: the native calibrated reference. -/
theorem calibrated_reference_native (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, ∃ q : Euc d → ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ h : ℕ → Euc d → ℝ,
        CalibratedReferenceData d a beta rho q h C := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0.le hsd ha hbeta
  set rho0 := HRS.Whole.thermalDensity d (criticalS d) a beta with hrho0
  have hρ0 : HRS.Whole.IsProbDensity rho0 := hT.prob
  have hM : ∀ x, rho0 x ≤ Cth := by
    intro x
    have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : Real.exp (-cth * ‖x‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hT.hc, sq_nonneg ‖x‖])
    nlinarith [hT.C0]
  obtain ⟨tau, htau, hsm⟩ := HRS.MS.S82R.s82r_tau_exists hs0 hsd hbeta Cth
  have hq := HRS.MS.S82R.s82r_qTau_shortRange hd1 htau
  have hΨ := featMap_hyp (d := d) hs0 htau
  have hκ : KappaSmall beta (wr13e_a d (criticalS d) tau Cth) := by
    have h0 : 0 ≤ beta * wr13e_a d (criticalS d) tau Cth :=
      mul_nonneg hbeta.le (wr13e_a_nonneg hs0 hsd htau Cth)
    exact wr11b_kappaSmall_of_le h0 (hsm.trans HRS.MS.S82R.s82r_one_thousand_le)
  obtain ⟨N0a, hN0a1, hfs⟩ := wr14a_field_small hd1 hs0 hsd htau beta Cth
  obtain ⟨CR0, N3, hL2⟩ := wr13e_reference_marginal_density_L2 hd1 hs0 hsd htau beta Cth hbeta hκ hΨ
  have hUnif := wr13e_reference_marginal_density_uniform hd hs0 hsd htau beta Cth hbeta hκ hΨ
  set CR : ℝ := max CR0 0 with hCR
  set N0 : ℕ := max (max N0a N3) 2 with hN0
  have hN02 : 2 ≤ N0 := le_max_right _ _
  have hN0a : N0a ≤ N0 := (le_max_left _ _).trans (le_max_left _ _)
  have hN03 : N3 ≤ N0 := (le_max_right _ _).trans (le_max_left _ _)
  have hcan : ∀ N, canonicalP d N a beta =
      HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d (criticalS d)) N beta
        (HRS.Whole.withDensityReal rho0) := fun N =>
    HRS.MS.Can2.can2_clause1_pos hd hs0 hsd ha hbeta N
  have hδnn : ∀ N : ℕ, 1 ≤ N → 0 ≤ deltaN N := fun N hN => HRS.MS.S82R.s82r_deltaN_nonneg hN
  have hctx : HRS.MS.S82R.S82RCtx d a beta rho0 Cth tau CR N0 := by
    refine ⟨hd, hbeta, hρ0, hM, htau, hsm, hN02, le_max_right _ _, ?_, ?_, ?_, hcan⟩
    · intro N hN x
      exact hfs hρ0 hM hbeta le_rfl (hN0a.trans hN) x
    · intro N hN
      obtain ⟨h1, h2⟩ := hL2 rho0 hρ0 hM beta hbeta le_rfl N (hN03.trans hN)
      refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      have : 0 ≤ HRS.deltaN d (criticalS d) N := by
        rw [HRS.MS.S82R.s82r_deltaN_eq]; exact hδnn N (by omega)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
    · intro ε hε
      obtain ⟨N1, hN1⟩ := hUnif ε hε
      refine ⟨max N1 N0, fun N hN => ?_⟩
      exact (hN1 rho0 hρ0 hM beta hbeta le_rfl N ((le_max_left _ _).trans hN)).2
  set k0 := kTau d (criticalS d) tau 0 with hk0
  have hk0n : 0 ≤ k0 := kTau_nonneg hs0 htau 0
  set Cdom : ℝ := Real.exp (4 * beta * k0) + Real.exp (16 * beta * N0 * k0) with hCdom
  set C : ℝ := 1 + 4 * beta * k0 * CR + Cdom + Real.exp (2 / 1000) * N0 + CR with hCdef
  have hCR0 : 0 ≤ CR := le_max_right _ _
  have hC1 : 1 ≤ C := by
    have h1 : 0 ≤ 4 * beta * k0 * CR := by positivity
    have h2 : 0 ≤ Cdom := by rw [hCdom]; positivity
    have h3 : 0 ≤ Real.exp (2 / 1000) * N0 := by positivity
    rw [hCdef]; linarith
  have hCf : 4 * beta * k0 * CR ≤ C := by
    have h2 : 0 ≤ Cdom := by rw [hCdom]; positivity
    have h3 : 0 ≤ Real.exp (2 / 1000) * N0 := by positivity
    rw [hCdef]; linarith
  have hCd1 : Real.exp (4 * beta * k0) ≤ C := by
    have h1 : 0 ≤ 4 * beta * k0 * CR := by positivity
    have h3 : 0 ≤ Real.exp (2 / 1000) * N0 := by positivity
    have h4 : 0 ≤ Real.exp (16 * beta * N0 * k0) := (Real.exp_pos _).le
    rw [hCdef, hCdom]; linarith
  have hCd2 : Real.exp (16 * beta * N0 * k0) ≤ C := by
    have h1 : 0 ≤ 4 * beta * k0 * CR := by positivity
    have h3 : 0 ≤ Real.exp (2 / 1000) * N0 := by positivity
    have h4 : 0 ≤ Real.exp (4 * beta * k0) := (Real.exp_pos _).le
    rw [hCdef, hCdom]; linarith
  have hCm : CR ≤ C := by
    have h1 : 0 ≤ 4 * beta * k0 * CR := by positivity
    have h2 : 0 ≤ Cdom := by rw [hCdom]; positivity
    have h3 : 0 ≤ Real.exp (2 / 1000) * N0 := by positivity
    rw [hCdef]; linarith
  have hCs : Real.exp (2 / 1000) * N0 ≤ C := by
    have h1 : 0 ≤ 4 * beta * k0 * CR := by positivity
    have h2 : 0 ≤ Cdom := by rw [hCdom]; positivity
    rw [hCdef]; linarith
  refine ⟨C, qTau d (criticalS d) tau, by linarith, ?_⟩
  intro rho hrho
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  refine ⟨HRS.MS.S82R.s82r_field d rho0 beta tau N0, ?_⟩
  refine ⟨by linarith, hq, hctx.field_meas, ?_, fun N _ x => hctx.field_le_one x, hctx.small_row, ?_, ?_, ?_⟩
  · intro N hN x
    by_cases hNN : N0 ≤ N
    · refine (hctx.field_rate hNN x).trans ?_
      have hd0 := hδnn N (by omega)
      calc 4 * beta * k0 * (CR * deltaN N) = (4 * beta * k0 * CR) * deltaN N := by ring
        _ ≤ C * deltaN N := mul_le_mul_of_nonneg_right hCf hd0
    · rw [hctx.field_of_lt (not_le.1 hNN) x]
      simp only [abs_zero]
      exact mul_nonneg (by linarith) (hδnn N (by omega))
  · intro N hN
    by_cases hNN : N0 ≤ N
    · refine (hctx.dom_large hNN).trans ?_
      exact HRS.MS.S82R.s82r_smul_le _ (ENNReal.ofReal_le_ofReal hCd1)
    · have hN1 : 0 < N := by omega
      refine (hctx.dom_small hN1 (not_le.1 hNN)).trans ?_
      refine HRS.MS.S82R.s82r_smul_le _ (ENNReal.ofReal_le_ofReal ?_)
      refine le_trans (Real.exp_le_exp.2 ?_) hCd2
      have hNle : (N : ℝ) ≤ N0 := by exact_mod_cast (not_le.1 hNN).le
      have : 0 ≤ beta * k0 := mul_nonneg hbeta.le hk0n
      nlinarith
  · intro N hN
    by_cases hNN : N0 ≤ N
    · refine (hctx.relL2_large hNN).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right hCm (hδnn N (by omega))
    · have hN1 : 0 < N := by omega
      refine (hctx.relL2_small hN1 (not_le.1 hNN)).trans (ENNReal.ofReal_le_ofReal ?_)
      have hg := HRS.MS.S82R.s82r_delta_ge (N := N) (by omega)
      have hNle : (N : ℝ) ≤ N0 := by exact_mod_cast (not_le.1 hNN).le
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
      have hN0pos : (0 : ℝ) < N0 := by exact_mod_cast (by omega : 0 < N0)
      have h1 : 1 / (N0 : ℝ) ≤ deltaN N := by
        refine le_trans ?_ hg
        exact one_div_le_one_div_of_le hNpos hNle
      calc Real.exp (2 / 1000) = Real.exp (2 / 1000) * N0 * (1 / (N0 : ℝ)) := by field_simp
        _ ≤ C * deltaN N := by
            refine mul_le_mul hCs h1 (by positivity) (by linarith)
  · exact hctx.relative_small

end HRS.MS.Phase2S82

end
