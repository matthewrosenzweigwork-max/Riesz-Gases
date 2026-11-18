import HRS.MS.S82RB3
import HRS.MS.QsfCorr2

/-!
# S8.2 R01B (S82R): `finite_pin_reference_adapter` (frozen statement of the Pro skeleton `S82.R01B`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82r_smul_le {E : Type*} [MeasurableSpace E] (ν : Measure E) {c c' : ℝ≥0∞} (hc : c ≤ c') :
    c • ν ≤ c' • ν := by
  refine Measure.le_iff'.2 fun s => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_left hc _

lemma s82r_deltaN_nonneg {N : ℕ} (hN : 1 ≤ N) : 0 ≤ HRS.MS.Phase2S82.deltaN N := by
  unfold HRS.MS.Phase2S82.deltaN HRS.MS.Phase2S82.logN
  refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg N)
  have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

end HRS.MS.S82R

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- R01B: the finite-pin adapter. -/
theorem finite_pin_reference_adapter (d : ℕ) (hd : 2 ≤ d)
    (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (q : Euc d → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      CalibratedReferenceData d a beta rho q h C0 →
      WeakReferenceSetup d a beta rho q h C := by
  set C : ℝ := |C0| + 2 + Real.exp (1 + 1 / 1000 + 1 + 1 / 1000) + 1 with hCdef
  have hexp : 0 < Real.exp (1 + 1 / 1000 + 1 + 1 / 1000) := Real.exp_pos _
  have hC0 : C0 ≤ C := by
    have := le_abs_self C0
    rw [hCdef]; linarith [abs_nonneg C0]
  have hC2 : 2 ≤ C := by rw [hCdef]; linarith [abs_nonneg C0]
  have hCe : Real.exp (1 + 1 / 1000 + 1 + 1 / 1000) ≤ C := by
    rw [hCdef]; linarith [abs_nonneg C0]
  refine ⟨C, by linarith, ?_⟩
  intro rho hrho h hD
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  have hρ0 : HRS.Whole.IsProbDensity (HRS.Whole.thermalDensity d (criticalS d) a beta) := hT.prob
  have hρG : HRS.Whole.HasR2GaussianUpper (Cth + 1) cth
      (HRS.Whole.thermalDensity d (criticalS d) a beta) := by
    refine ⟨hT.hc, fun x => ?_⟩
    have h1 := (le_abs_self _).trans (hT.h0 x)
    have h2 : 0 ≤ Real.exp (-cth * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith
  have hG : 0 < Cth + 1 := by linarith [hT.C0]
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  set rho := HRS.Whole.thermalDensity d (criticalS d) a beta with hrho
  have hsmallpos : ∀ N, 2 ≤ N → 0 ≤ deltaN N := fun N hN =>
    HRS.MS.S82R.s82r_deltaN_nonneg (by omega)
  refine ⟨by linarith, hD.short, hD.hmeas, ?_, hD.small_row, ?_, ?_, ?_, ?_, ?_, hD.relative_small⟩
  · intro N hN x
    exact (hD.hbound N hN x).trans (mul_le_mul_of_nonneg_right hC0 (hsmallpos N hN))
  · intro N hN p n hp hnp pins
    haveI := HRS.MS.S82R.s82r_isProb hρ0
    have hlam : 0 ≤ beta / (N : ℝ) := div_nonneg hbeta.le (Nat.cast_nonneg N)
    rw [HRS.MS.S82R.s82r_referenceLaw_eq hd hbeta hD hG hρ0 hρG hN pins]
    exact HRS.External.isProb_pinnedLaw _ hlam n pins
  · intro N hN
    exact (hD.domination N hN).trans
      (HRS.MS.S82R.s82r_smul_le _ (ENNReal.ofReal_le_ofReal hC0))
  · intro N hN p n hp hnp pins i X
    refine (HRS.MS.S82R.s82r_conditional_core hd hbeta hD hG hρ0 hρG hN hnp pins i X).trans ?_
    exact HRS.MS.S82R.s82r_smul_le _ (ENNReal.ofReal_le_ofReal hCe)
  · intro N hN p n hp hnp _ pins F hF
    refine (HRS.MS.S82R.s82r_resampling hd hbeta hD hG hρ0 hρG hN hnp pins F hF).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hC2) _
  · intro N hN
    exact (hD.relative_L2 N hN).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hC0 (hsmallpos N hN)))

end HRS.MS.Phase2S82

end
