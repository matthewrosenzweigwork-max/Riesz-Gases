import HRS.MS.Fp81S21PredMap3
import HRS.MS.R2InterpAux16

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- The transpose propagator at fixed source and terminal times, acting on
weighted chart coefficients. -/
def fp81s21_chartVprop
    {d r : ℕ} {Pw : ℝ} {C : WholeCoeff d} {m T : ℝ}
    {c : MultiIndex d → ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (E : r26t6_WeightedChart d r Pw)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) :
    r26t6_Coeff →L[ℝ] OscDual d m :=
  ({ toFun := fun z => r2Vprop C m t u (fp81s21_chartAction E z)
     map_add' := by
       intro z z'
       apply s102_ext
       intro α
       rw [s102_Vprop_coord hP hD (fp81s21_chartAction_S102Z E (z + z')) hlin hu ht,
         OscDual.coord_add,
         s102_Vprop_coord hP hD (fp81s21_chartAction_S102Z E z) hlin hu ht,
         s102_Vprop_coord hP hD (fp81s21_chartAction_S102Z E z') hlin hu ht]
       simp [fp81s21_chartAction, inner_add_left]
     map_smul' := by
       intro a z
       apply s102_ext
       intro α
       rw [s102_Vprop_coord hP hD (fp81s21_chartAction_S102Z E (a • z)) hlin hu ht,
         OscDual.coord_smul,
         s102_Vprop_coord hP hD (fp81s21_chartAction_S102Z E z) hlin hu ht]
       simp [fp81s21_chartAction, inner_smul_left] } :
      r26t6_Coeff →ₗ[ℝ] OscDual d m).mkContinuous (s102_KV d r Pw c) (by
        intro z
        change ‖r2Vprop C m t u (fp81s21_chartAction E z)‖ ≤ s102_KV d r Pw c * ‖z‖
        have h := s102_Vprop_norm_M hP hD (fp81s21_chartAction_S102Z E z) hlin
          (fp81s21_chartAction_weighted_bound E z) hu ht
        simpa only [abs_norm, mul_comm] using h)

/-- A bound uniform over all source and terminal times covered by the same
summable orbit envelope. -/
theorem fp81s21_chartVprop_norm_le
    {d r : ℕ} {Pw : ℝ} {C : WholeCoeff d} {m T : ℝ}
    {c : MultiIndex d → ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (E : r26t6_WeightedChart d r Pw)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) :
    ‖fp81s21_chartVprop hP hD hlin E hu ht‖ ≤ s102_KV d r Pw c := by
  apply ContinuousLinearMap.opNorm_le_bound _ (s102_KV_nonneg d r Pw c)
  intro z
  change ‖r2Vprop C m t u (fp81s21_chartAction E z)‖ ≤ s102_KV d r Pw c * ‖z‖
  have h := s102_Vprop_norm_M hP hD (fp81s21_chartAction_S102Z E z) hlin
    (fp81s21_chartAction_weighted_bound E z) hu ht
  simpa only [abs_norm, mul_comm] using h

#print axioms HRS.Fp81.S21.fp81s21_chartVprop
#print axioms HRS.Fp81.S21.fp81s21_chartVprop_norm_le

end HRS.Fp81.S21
