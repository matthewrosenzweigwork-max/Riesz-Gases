import HRS.MS.Fp81S21JointG3

/-! Combining the two coordinate projection errors in the product norm. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
namespace HRS.Fp81.S21

/-- Coordinate mean-square bounds combine into a product mean-square bound. -/
theorem fp81s21_jointG_pair_sqerr
    {Ω V W : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [NormedAddCommGroup W]
    (P : Measure Ω) (f g : Ω → V) (u v : Ω → W) (ε η : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hf : fp81s21_SqErr P f g ε) (hu : fp81s21_SqErr P u v η) :
    fp81s21_SqErr P (fun ω => (f ω, u ω)) (fun ω => (g ω, v ω)) (ε + η) := by
  let F : Ω → ℝ := fun ω => ‖f ω - g ω‖ ^ 2
  let U : Ω → ℝ := fun ω => ‖u ω - v ω‖ ^ 2
  have heq : (fun ω => ‖(f ω, u ω) - (g ω, v ω)‖ ^ 2) =
      fun ω => max (F ω) (U ω) := by
    funext ω
    change (max ‖f ω - g ω‖ ‖u ω - v ω‖) ^ 2 =
      max (‖f ω - g ω‖ ^ 2) (‖u ω - v ω‖ ^ 2)
    by_cases h : ‖f ω - g ω‖ ≤ ‖u ω - v ω‖
    · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (norm_nonneg _) h 2)]
    · have h' : ‖u ω - v ω‖ ≤ ‖f ω - g ω‖ := le_of_not_ge h
      rw [max_eq_left h', max_eq_left (pow_le_pow_left₀ (norm_nonneg _) h' 2)]
  have hbound : ∀ ω, max (F ω) (U ω) ≤ F ω + U ω := by
    intro ω
    exact max_le (le_add_of_nonneg_right (sq_nonneg _)) (le_add_of_nonneg_left (sq_nonneg _))
  have hmax : Integrable (fun ω => max (F ω) (U ω)) P := by
    apply (hf.1.add hu.1).mono' ((hf.1.aestronglyMeasurable.aemeasurable.max hu.1.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_of_le_left (sq_nonneg _))]
    exact hbound ω
  rw [fp81s21_SqErr, heq]
  refine ⟨hmax, ?_⟩
  calc
    ∫ ω, max (F ω) (U ω) ∂P ≤ ∫ ω, (F ω + U ω) ∂P :=
      integral_mono_ae hmax (hf.1.add hu.1) (Filter.Eventually.of_forall hbound)
    _ = (∫ ω, F ω ∂P) + ∫ ω, U ω ∂P := integral_add hf.1 hu.1
    _ ≤ ε ^ 2 + η ^ 2 := add_le_add hf.2 hu.2
    _ ≤ (ε + η) ^ 2 := by nlinarith

#print axioms fp81s21_jointG_pair_sqerr
end HRS.Fp81.S21
end
