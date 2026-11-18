import HRS.MS.Fp81S21NoisePath6
import HRS.MS.Fp81S21WindowSup13
import HRS.MS.Fp81S21WindowSup54
import HRS.MS.Fp81S21DriftPrimitive9

/-! Lower-integral conversion for nonnegative sixth moments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21

/-- A finite lower-integral bound for a measurable sixth power is a genuine
sixth moment bound. -/
theorem fp81s21_moment6_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (M : ℝ)
    (hY : AEMeasurable Y P) (hM : 0 ≤ M)
    (hbound : (∫⁻ ω, ENNReal.ofReal (‖Y ω‖ ^ 6) ∂P) ≤ ENNReal.ofReal M) :
    fp81s21_Moment6 P Y M := by
  have hm : AEStronglyMeasurable (fun ω => ‖Y ω‖ ^ 6) P :=
    (hY.norm.pow_const 6).aestronglyMeasurable
  have hn : ∀ ω, 0 ≤ ‖Y ω‖ ^ 6 := fun ω => pow_nonneg (norm_nonneg _) _
  have hi : Integrable (fun ω => ‖Y ω‖ ^ 6) P := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have he : (fun ω => ‖‖Y ω‖ ^ 6‖ₑ) =
        (fun ω => ENNReal.ofReal (‖Y ω‖ ^ 6)) := by
      funext ω
      exact Real.enorm_eq_ofReal (hn ω)
    rw [he]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hY, hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)
  apply ENNReal.ofReal_le_ofReal_iff hM |>.mp
  exact he.trans_le hbound

#print axioms fp81s21_moment6_of_lintegral
end HRS.Fp81.S21
end
