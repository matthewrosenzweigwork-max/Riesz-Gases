import HRS.MS.PROS15dTiltTransfer
import HRS.MS.S21G2_K11b

/-!
# R26-T3.S15d: quantitative fourth-to-second moment estimate after tilting

The explicit constant is the square root of the second exponential moment,
divided by the positive normalizing partition function. This gives the
continuity of first-chaos projection from L4(P) to L2(P_tilt).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_tilted_second_moment_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V F : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hF4 : MemLp F 4 P) :
    ∫ ω, F ω ^ 2 ∂(r26t3_tilt P V) ≤
      (∫ ω, Real.exp (-V ω) ∂P)⁻¹ *
        (Real.sqrt (∫ ω, F ω ^ 4 ∂P) *
          Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P)) := by
  have hWeight : MemLp (fun ω => Real.exp (-V ω)) 2 P := by
    refine (memLp_two_iff_integrable_sq
      (Real.measurable_exp.comp_aemeasurable hV.neg).aestronglyMeasurable).2 ?_
    refine hExp2.congr (ae_of_all _ fun ω => ?_)
    change Real.exp (-(2 * V ω)) = Real.exp (-V ω) ^ 2
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hF2 : MemLp (fun ω => F ω ^ 2) 2 P := by
    have heq : (F * F) = (fun ω => F ω ^ 2) := by
      funext ω
      simp [Pi.mul_apply, pow_two]
    simpa only [heq] using (hF4.mul hF4 (r := 2))
  have hCS := s21g2_k11b_cs hF2 hWeight
  have hI : ∫ ω, F ω ^ 2 * Real.exp (-V ω) ∂P ≤
      Real.sqrt (∫ ω, F ω ^ 4 ∂P) *
        Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P) := by
    have hf : ∫ ω, (F ω ^ 2) ^ 2 ∂P = ∫ ω, F ω ^ 4 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    have he : ∫ ω, (Real.exp (-V ω)) ^ 2 ∂P =
        ∫ ω, Real.exp (-(2 * V ω)) ∂P := by
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      change Real.exp (-V ω) ^ 2 = Real.exp (-(2 * V ω))
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hf, he] at hCS
    exact (le_abs_self _).trans hCS
  have hZ : 0 < ∫ ω, Real.exp (-V ω) ∂P :=
    s21g2_s15a_Z_pos P hV hExp1
  rw [r26t3_tilt_integral P hV hExp1]
  exact mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hZ.le)

end HRS.MS.R26T3
