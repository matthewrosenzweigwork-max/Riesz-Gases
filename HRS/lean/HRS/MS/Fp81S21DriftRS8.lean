import HRS.MS.Fp81S21RSValue4

/-! Measurability of variation for measurable continuous paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21

/-- Variation is a lower semicontinuous, hence measurable, functional on
continuous paths on a compact interval. -/
theorem fp81s21_continuous_path_variation_measurable
    {E : Type*} [NormedAddCommGroup E] (q r : ℝ) :
    Measurable (fun f : C(Icc q r, E) => eVariationOn f Set.univ) := by
  have h : LowerSemicontinuous
      (fun f : C(Icc q r, E) => eVariationOn f Set.univ) := by
    intro f
    apply eVariationOn.lowerSemicontinuous_aux
    intro x hx
    exact (continuous_eval_const x).continuousAt.tendsto
  exact h.measurable

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_continuous_path_variation_measurable
