import HRS.MS.SA16JetConv

/-!
# S8.2 observed-time layer, packet T8A.B00 (Minkowski helper): L² bound of a time integral

For a jointly measurable `G : Ω → ℝ → ℝ` and an interval `[l, h]`, the squared `L²(P)` norm of
`x ↦ ∫_{[l,h]} G x r dr` is at most `(h - l)` times `∫_{[l,h]} ‖G · r‖²_{L²(P)} dr`.  This is the weighted Minkowski
inequality `sa16j_mink` with the weight `1` on `[l, h]`, in the lintegral form that the sup-in-time bounds use.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A

theorem r26t8a_minkowski_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (l h : ℝ) {F : Ω → ℝ → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    ∫⁻ w, (∫⁻ r in Set.Icc l h, F w r) ^ (2 : ℝ) ∂P ≤
      (volume (Set.Icc l h)) * ∫⁻ r in Set.Icc l h, ∫⁻ w, F w r ^ (2 : ℝ) ∂P := by
  have hm : Measurable (Function.uncurry fun (w : Ω) (r : ℝ) => F w r) := hF
  have key := HRS.Whole.AppendixA.Phase2SA16.sa16j_mink (μ := P) (ν := (volume : Measure ℝ).restrict (Set.Icc l h))
    (p := 2) (by norm_num) (a := fun _ => (1 : ℝ≥0∞)) measurable_const hm
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at key
  simpa [Measure.restrict_apply_univ, lintegral_const, one_mul, Real.volume_Icc] using key

end HRS.MS.R26T8A

end
