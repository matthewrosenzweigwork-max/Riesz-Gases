import HRS.MS.SA16U3K10f

/-!
# S.A.16 K10, part (g): the combined identity `2 P_{lj} = S + D` (worker SA16U3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA HRS.CZ.Hls Phase2SA16

section K10g
variable {d : ℕ}

lemma sa16u3_main_identity (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) {Ba Bda : ℝ} (hBa : ∀ x, |a x| ≤ Ba)
    (hBda : ∀ x, ‖fderiv ℝ a x‖ ≤ Bda) (Z Zl Zj : SchwartzMap (Euc d) ℝ) (el ej : Euc d)
    (hl : ∀ x, Zl x = fderiv ℝ Z x el) (hj : ∀ x, Zj x = fderiv ℝ Z x ej)
    (hmix : ∀ y, fderiv ℝ (⇑Zj) y el = fderiv ℝ (⇑Zl) y ej) :
    2 * ∫ x, Zl x * a x * spliceOdd d θ δ i (⇑Zj) x =
      -(∫ x, Zl x * (spliceOdd d θ δ i (fun y => a y * Zj y) x -
            a x * spliceOdd d θ δ i (⇑Zj) x)) +
        (-(∫ x, fderiv ℝ a x el * spliceOdd d θ δ i (⇑Zj) x * Z x) +
          ∫ x, fderiv ℝ a x ej * spliceOdd d θ δ i (⇑Zl) x * Z x) := by
  have hS := sa16u3_sym_identity hd hθ1 hδ i ha.continuous hBa Zl Zj
  have h1 := sa16u3_ibp hd hθ1 hδ i ha hBa hBda Z Zj el
  have h2 := sa16u3_ibp hd hθ1 hδ i ha hBa hBda Z Zl ej
  have hfun : (fun y => fderiv ℝ (⇑Zj) y el) = fun y => fderiv ℝ (⇑Zl) y ej := funext hmix
  rw [hfun] at h1
  have e1 : (fun x => fderiv ℝ Z x el * a x * spliceOdd d θ δ i (⇑Zj) x) =
      fun x => Zl x * a x * spliceOdd d θ δ i (⇑Zj) x := funext fun x => by rw [hl]
  have e2 : (fun x => fderiv ℝ Z x ej * a x * spliceOdd d θ δ i (⇑Zl) x) =
      fun x => Zj x * a x * spliceOdd d θ δ i (⇑Zl) x := funext fun x => by rw [hj]
  rw [e1] at h1
  rw [e2] at h2
  linarith

end K10g
end HRS.Whole.AppendixA.Phase2SA16Cutoff
