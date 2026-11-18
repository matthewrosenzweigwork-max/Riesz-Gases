import HRS.MS.Fp81S21SmoothSqErr

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.Fp81.S21

/-- The explicit common smoothing profile and averaging-operator bounds on a
fixed positive horizon. -/
theorem fp81s21_avgPackage_profile
    (H D : ℝ) (hH : 0 < H) (hD : 0 ≤ D) :
    (∀ k : ℕ, 0 ≤ Real.sqrt D *
      (H / ((k : ℝ) + 2)) ^ (1 / 8 : ℝ)) ∧
    Tendsto (fun k : ℕ => Real.sqrt D *
      (H / ((k : ℝ) + 2)) ^ (1 / 8 : ℝ)) atTop (𝓝 0) ∧
    (∀ k : ℕ,
      ‖fp81s21_avgOperator H hH k‖ ≤ Real.sqrt (((k : ℝ) + 2) / H)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    apply mul_nonneg (Real.sqrt_nonneg D)
    apply Real.rpow_nonneg
    apply div_nonneg hH.le
    positivity
  · simpa [fp81s21_avgHalfWidth] using
      fp81s21_smoothSqErrProfile_tendsto H D hH hD
  · intro k
    exact fp81s21_avgOperator_opNorm_le H hH k

#print axioms fp81s21_avgPackage_profile

end HRS.Fp81.S21
