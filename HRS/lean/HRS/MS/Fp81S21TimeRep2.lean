import HRS.MS.Fp81S21TimeRep
import HRS.MS.Fp81S21EmbedField9

/-! Pointwise projections on the time-L² coefficient space. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS.MS.R26T6

/-- Lift the coefficient projection to the time-L² space. -/
def fp81s21_timeProject (H : ℝ) (m : ℕ) :
    Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)) →L[ℝ]
      Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)) :=
  (fp81s21_projectField m).compLpL 2 (volume.restrict (Set.Icc (0 : ℝ) H))

/-- The lift applies the coefficient projection almost everywhere. -/
theorem fp81s21_timeProject_apply (H : ℝ) (m : ℕ)
    (v : Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) H)),
      fp81s21_timeProject H m v t = fp81s21_projectField m (v t) := by
  exact (fp81s21_projectField m).coeFn_compLpL v

/-- The lifted projection is a contraction. -/
theorem fp81s21_timeProject_norm_le (H : ℝ) (m : ℕ) :
    ‖fp81s21_timeProject H m‖ ≤ 1 := by
  have hp : ‖fp81s21_projectField m‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simpa using fp81s21_projectField_norm_le m z
  exact le_trans ((fp81s21_projectField m).norm_compLpL_le) hp

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_timeProject
#print axioms HRS.Fp81.S21.fp81s21_timeProject_apply
#print axioms HRS.Fp81.S21.fp81s21_timeProject_norm_le
