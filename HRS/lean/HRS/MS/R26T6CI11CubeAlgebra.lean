import HRS.MS.R26T6CI11CubeTime

/-! I11: cubic algebra and fractional-power identities for path moments. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C

theorem r26t6c_sum_cube_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  have h := mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))
  nlinarith

theorem r26t6c_time_power_cube (T : ℝ) (hT : 0 ≤ T) :
    (T ^ (2 / 3 : ℝ)) ^ 3 = T ^ 2 := by
  calc
    _ = (T ^ (2 / 3 : ℝ)) ^ (3 : ℝ) :=
      (Real.rpow_natCast (T ^ (2 / 3 : ℝ)) 3).symm
    _ = T ^ ((2 / 3 : ℝ) * 3) := (Real.rpow_mul hT _ _).symm
    _ = T ^ (2 : ℕ) := by norm_num

end HRS.MS.R26T6C
