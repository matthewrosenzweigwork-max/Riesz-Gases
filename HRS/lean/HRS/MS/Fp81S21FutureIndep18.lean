import HRS.MS.Fp81S21FutureIndep9
import HRS.MS.Fp81S21FutureIndep2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- The past part of every terminal observation lies in the complete
cutoff-past source space, including for terminal times after the cutoff. -/
theorem fp81s21_past_feature_supported
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ} (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ ∈
      fp81s21_PastNoiseFeatures p.d r := by
  have hp := fp81s21_movingNoise_past_feature_ae p R hδ hδhalf hH hr ht hφ
  filter_upwards [hp] with q hq hqr
  rw [hq]
  simp [not_le_of_gt hqr]

#print axioms fp81s21_past_feature_supported

end HRS.Fp81.S21
end
