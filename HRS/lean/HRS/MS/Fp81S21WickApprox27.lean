import HRS.MS.Fp81S21WickApprox26
import HRS.MS.Fp81S21WickApprox8

/-! Time sections of projected fields. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
namespace HRS.Fp81.S21
open HRS.MS.R26T6

local instance fp81s21_wickApprox27_measSpace (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_wickApprox27_borelSpace (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Projecting a genuine time section gives a genuine time section of the
projected coefficient field, with the same second-moment bound. -/
theorem fp81s21_TimeL2Rep_project2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (m : ℕ)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hU : fp81s21_TimeL2Rep P q M a H U) :
    fp81s21_TimeL2Rep P (fun u ω => fp81s21_projectField m (q u ω)) M a H
      (fun ω => fp81s21_timeProject H m (U ω)) := by
  have hL : MemLp (fun ω => fp81s21_timeProject H m (U ω)) 2 P :=
    hU.2.1.continuousLinearMap_comp (fp81s21_timeProject H m)
  refine ⟨(fp81s21_timeProject H m).continuous.measurable.comp hU.1, hL, ?_, ?_⟩
  · calc
      _ ≤ ∫ ω, ‖U ω‖ ^ 2 ∂P := by
        apply integral_mono (hL.integrable_norm_pow (by norm_num))
          (hU.2.1.integrable_norm_pow (by norm_num))
        intro ω
        apply pow_le_pow_left₀ (norm_nonneg _)
        calc
          ‖fp81s21_timeProject H m (U ω)‖ ≤ ‖fp81s21_timeProject H m‖ * ‖U ω‖ :=
            (fp81s21_timeProject H m).le_opNorm _
          _ ≤ 1 * ‖U ω‖ := mul_le_mul_of_nonneg_right
            (fp81s21_timeProject_norm_le H m) (norm_nonneg _)
          _ = ‖U ω‖ := one_mul _
      _ ≤ H * M := hU.2.2.1
  · filter_upwards [hU.2.2.2] with ω hω
    refine ⟨hω.1.continuousLinearMap_comp (fp81s21_projectField m), ?_⟩
    filter_upwards [fp81s21_timeProject_apply H m (U ω), hω.2] with t hp he
    rw [hp, he]

#print axioms fp81s21_TimeL2Rep_project2
end HRS.Fp81.S21
end
