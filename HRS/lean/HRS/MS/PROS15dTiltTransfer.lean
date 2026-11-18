import HRS.MS.PROS15dTiltHolder

/-!
# R26-T3.S15d: transfer L4 integrability to L2 under a Gaussian tilt

This is the quantitative-continuity mechanism for first-chaos approximation
under a square-integrable likelihood. Unlike a formal identity of expectations,
the conclusion proves genuine L2 integrability under the changed measure.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_L4_to_tilted_L2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {V F : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hF4 : MemLp F 4 P) :
    MemLp F 2 (r26t3_tilt P V) := by
  have hWeight := s15d_weighted_square_integrable hV hExp2 hF4
  have hExpMeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp (-V ω))) P :=
    (Real.measurable_exp.comp_aemeasurable hV.neg).ennreal_ofReal
  have hWith : Integrable (fun ω => F ω ^ 2)
      (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (-V ω)))) := by
    rw [integrable_withDensity_iff_integrable_smul₀' hExpMeas
      (ae_of_all _ fun ω => ENNReal.ofReal_lt_top)]
    refine hWeight.congr (ae_of_all _ fun ω => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    ring
  have hZ : 0 < ∫ ω, Real.exp (-V ω) ∂P :=
    s21g2_s15a_Z_pos P hV hExp1
  have hI : Integrable (fun ω => F ω ^ 2) (r26t3_tilt P V) := by
    unfold r26t3_tilt
    apply Integrable.smul_measure hWith
    exact ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne'
  have hAC : r26t3_tilt P V ≪ P := by
    unfold r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous P _ hs]
  have hF : AEStronglyMeasurable F (r26t3_tilt P V) :=
    hF4.aestronglyMeasurable.mono_ac hAC
  exact (memLp_two_iff_integrable_sq hF).2 hI

end HRS.MS.R26T3
