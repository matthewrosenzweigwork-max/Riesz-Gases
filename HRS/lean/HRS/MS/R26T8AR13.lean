import HRS.MS.R26T8AR08
import HRS.MS.R26T8AR10
import HRS.MS.R26T8AR11

/-!
# S8.2 observed-time layer, packet T8A.R13: exact `WeakReferenceSetup` from the calibration (corrected version)
Statement as in the Pro packet plus `(ha : 0 < a)` (already present in the packet signature) and with the constant
`C = max (max C0 2) (exp (2 + 2/1000))`.  Probability from R08, conditional domination from R10 (`_pos` version),
resampling from R11 (`_pos` version, which already handles an arbitrary `MemLp` representative, so the packet's R12 transfer
lemma is not needed; as stated R12 also lacks a measurability hypothesis on the kernel `K`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_finite_pin_reference_adapter (d : ℕ) (hd : 2 ≤ d)
    (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (q : Euc d → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      CalibratedReferenceData d a beta rho q h C0 →
      WeakReferenceSetup d a beta rho q h C := by
  set C : ℝ := max (max C0 2) (Real.exp (2 + 2 / 1000)) with hC
  have hC0 : C0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC2 : (2 : ℝ) ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCe : Real.exp (2 + 2 / 1000) ≤ C := le_max_right _ _
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun rho hrho h hcal => ?_⟩
  have hdelta : ∀ N : ℕ, 0 ≤ Phase2S82.deltaN N := fun N => by
    unfold Phase2S82.deltaN Phase2S82.logN
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
      have : (1 : ℝ) ≤ N := by exact_mod_cast h0
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith
  obtain ⟨-, G0, c, hG0, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hG : HRS.Whole.HasR2GaussianUpper (G0 + 1) c rho := ⟨hc, fun x => by
    have h1 := (le_abs_self (rho x)).trans (hb x).1
    nlinarith [Real.exp_pos (-c * ‖x‖ ^ 2)]⟩
  refine ⟨hCpos, hcal.short, hcal.hmeas, ?_, hcal.small_row, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N hN x
    exact (hcal.hbound N hN x).trans (mul_le_mul_of_nonneg_right hC0 (hdelta N))
  · intro N hN p n hp hnp pins
    obtain ⟨hint, hpos⟩ := r26t8a_pinned_partition hd hbeta hrho hcal N hN hnp pins
    refine ⟨?_⟩
    unfold referenceLaw exponentialTilt
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top
  · intro N hN
    refine (hcal.domination N hN).trans (Measure.le_iff.2 fun s hs => ?_)
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
  · intro N hN p n hp hnp pins i X
    refine (r26t8a_conditional_repulsion_pos hd ha hbeta hrho hcal N hN hnp pins i X).trans
      (Measure.le_iff.2 fun s hs => ?_)
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    gcongr
  · intro N hN p n hp hnp hNn pins F hF
    have := HRS.MS.S82R.s82r_resampling hd hbeta hcal (G := G0 + 1) (c := c) (by linarith)
      hrho.2.1 hG hN hnp pins F hF
    refine this.trans ?_
    gcongr
  · intro N hN
    refine (hcal.relative_L2 N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right hC0 (hdelta N)
  · exact hcal.relative_small

end HRS.MS.R26T8A
