import HRS.MS.PROS15dTiltSquare
import HRS.MS.S21G2_K11b

/-!
# R26-T3.S15d: Hölder integrability of quadratic first-chaos observables
under an exponentially tilted Gaussian probability measure.

This general result is independent of the particular kernel. A square-integrable
unnormalized likelihood and an L4 observable imply integrability of its
squared observable against the unnormalized likelihood.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_weighted_square_integrable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V F : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hF4 : MemLp F 4 P) :
    Integrable (fun ω => F ω ^ 2 * Real.exp (-V ω)) P := by
  have hExpSq : Integrable (fun ω => (Real.exp (-V ω)) ^ 2) P := by
    refine hExp2.congr ?_
    filter_upwards [] with ω
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hExpMeas : AEStronglyMeasurable (fun ω => Real.exp (-V ω)) P :=
    (Real.measurable_exp.comp_aemeasurable hV.neg).aestronglyMeasurable
  have hExpLp : MemLp (fun ω => Real.exp (-V ω)) 2 P :=
    (memLp_two_iff_integrable_sq hExpMeas).2 hExpSq
  have hF2 : MemLp (fun ω => F ω ^ 2) 2 P := by
    have heq : (F * F) = (fun ω => F ω ^ 2) := by
      funext ω
      simp [Pi.mul_apply, pow_two]
    simpa only [heq] using (hF4.mul hF4 (r := 2))
  exact hF2.integrable_mul hExpLp

end HRS.MS.R26T3
