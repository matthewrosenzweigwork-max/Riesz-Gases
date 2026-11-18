import HRS.MS.Fp81S21WindowSup36

/-! Scalar integrability from a sixth-moment bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace HRS.Fp81.S21

/-- A measurable random variable with finite sixth moment is integrable. -/
theorem fp81s21_integrable_of_sixth
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (M : ℝ) (hSix : SixthBound P Y M) :
    Integrable Y P := by
  have hMem : MemLp Y (ENNReal.ofReal 6) P := by
    apply (integrable_norm_rpow_iff hY.aestronglyMeasurable
      (by norm_num) (by norm_num)).1
    simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6)] using hSix.1
  exact hMem.integrable (by norm_num)

#print axioms fp81s21_integrable_of_sixth
end HRS.Fp81.S21
end
