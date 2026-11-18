import HRS.MS.R26T6CI11Cube

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_Lp_norm_cube
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U : Lp ℝ 3 μ) :
    ‖U‖ ^ 3 = ∫ x, |(U : X → ℝ) x| ^ 3 ∂μ := by
  simpa only [Lp.norm_def, lpNorm, Real.norm_eq_abs] using
    (r26t6c_vector_lpNorm_cube μ (U : X → ℝ) (Lp.memLp U))

end HRS.MS.R26T6C
