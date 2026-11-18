import HRS.MS.S21G2_S15a

/-!
# S15d: the normalized exponential tilt depends only on the a.e. class

This allows the physical Wick representative to be replaced by its
canonical Gaussian quadratic representative without changing the tilted
probability measure.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_tilt_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (V W : Ω → ℝ) (hVW : V =ᵐ[P] W) :
    r26t3_tilt P V = r26t3_tilt P W := by
  have hExp : (fun ω => Real.exp (-V ω)) =ᵐ[P]
      (fun ω => Real.exp (-W ω)) :=
    hVW.mono (fun ω hω => by
      simpa using congrArg (fun x : ℝ => Real.exp (-x)) hω)
  have hWeight : (fun ω => ENNReal.ofReal (Real.exp (-V ω))) =ᵐ[P]
      (fun ω => ENNReal.ofReal (Real.exp (-W ω))) :=
    hVW.mono (fun ω hω => by
      simpa using congrArg (fun x : ℝ => ENNReal.ofReal (Real.exp (-x))) hω)
  unfold r26t3_tilt
  rw [integral_congr_ae hExp, withDensity_congr_ae hWeight]

end HRS.MS.R26T3
