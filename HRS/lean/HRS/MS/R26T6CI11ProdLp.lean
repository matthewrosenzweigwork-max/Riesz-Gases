import HRS.MS.R26T6CI11Section
import Mathlib.MeasureTheory.Integral.Prod

/-!
# I11: a joint L³ estimate from uniform sectional L³ bounds.

The measure on the first factor need only be finite. No pointwise bound
on G or independence assumption is made.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_spacetime_L3_of_sections
    {Time Omega B : Type*} [MeasurableSpace Time] [MeasurableSpace Omega]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (dt : Measure Time) [IsFiniteMeasure dt]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Time × Omega → B)
    (hG : AEStronglyMeasurable G (dt.prod P))
    (A : ℝ) (hA : 0 ≤ A)
    (hsec : ∀ᵐ t ∂dt, MemLp (fun w => G (t,w)) 3 P ∧
      eLpNorm (fun w => G (t,w)) 3 P ≤ ENNReal.ofReal A) :
    MemLp G 3 (dt.prod P) := by
  have hm : AEMeasurable (fun z => ‖G z‖ₑ ^ (3 : ℝ)) (dt.prod P) :=
    hG.enorm.pow_const _
  have hlin : (∫⁻ z, ‖G z‖ₑ ^ (3 : ℝ) ∂(dt.prod P)) =
      ∫⁻ t, (∫⁻ w, ‖G (t,w)‖ₑ ^ (3 : ℝ) ∂P) ∂dt :=
    lintegral_prod _ hm
  have hpoint : ∀ᵐ t ∂dt,
      (∫⁻ w, ‖G (t,w)‖ₑ ^ (3 : ℝ) ∂P) ≤
        ENNReal.ofReal A ^ (3 : ℝ) := by
    filter_upwards [hsec] with t ht
    obtain ⟨htL, htB⟩ := ht
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (by norm_num) (by norm_num) htL.aestronglyMeasurable] at htB
    have hh := ENNReal.rpow_le_rpow htB (by norm_num : (0 : ℝ) ≤ 3)
    simpa only [ENNReal.toReal_ofNat, show (1 / (3 : ℝ) * 3) = 1 by norm_num,
      ← ENNReal.rpow_mul, ENNReal.rpow_one] using hh
  have htfinite : (∫⁻ z, ‖G z‖ₑ ^ (3 : ℝ) ∂(dt.prod P)) < ∞ := by
    rw [hlin]
    calc
      _ ≤ ∫⁻ t, ENNReal.ofReal A ^ (3 : ℝ) ∂dt :=
        lintegral_mono_ae hpoint
      _ = dt Set.univ * ENNReal.ofReal A ^ (3 : ℝ) := by
        simp [lintegral_const, mul_comm]
      _ < ∞ := by
        have hpow : (ENNReal.ofReal A) ^ (3 : ℝ) ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_nonneg
            (by norm_num : (0 : ℝ) ≤ 3) ENNReal.ofReal_ne_top
        exact ENNReal.mul_lt_top ((measure_ne_top dt Set.univ).lt_top) hpow.lt_top
  apply (memLp_iff).2
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) hG).2
  simpa only [ENNReal.toReal_ofNat] using htfinite

end HRS.MS.R26T6C
