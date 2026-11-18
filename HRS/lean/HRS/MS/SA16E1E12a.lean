import HRS.MS.SA16E1Geo3

/-!
# S.A.16 E12 (part a): Lipschitz inverse of `charFlow` for every time, and joint measurability of the forward map
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.Whole.AppendixALemmas

theorem e12_charFlow_max (d : ℕ) (b : ℝ → Euc d → Euc d) (ν : ℝ) (w : ℝ≥0 → Fin d → ℝ) (t : ℝ) :
    charFlow d b ν w t = charFlow d b ν w (max t 0) := by
  funext x
  exact HRS.picardLim_max _ _ _ _ _

theorem e12_inv_lip (d : ℕ) (hd : 1 ≤ d) {B : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : DriftBounds d 1 B b) {ν : ℝ} (hν : 0 ≤ ν) {w : ℝ≥0 → Fin d → ℝ} (hw : Continuous w)
    (hw0 : w 0 = 0) (t : ℝ) :
    Function.Bijective (charFlow d b ν w t) ∧ Continuous (charFlow d b ν w t) ∧ ∃ L : ℝ, 0 ≤ L ∧ ∀ z z' : Euc d,
      ‖Function.invFun (charFlow d b ν w t) z - Function.invFun (charFlow d b ν w t) z'‖ ≤
        L * ‖z - z'‖ := by
  rw [e12_charFlow_max d b ν w t]
  obtain ⟨C, hC, h⟩ := charFlow_geometry d 1 hd le_rfl B (max t 0) (le_max_right _ _)
  obtain ⟨hbij, hcdX, hcd, hder, -⟩ := h b hb ν hν w hw hw0 (max t 0) ⟨le_max_right _ _, le_rfl⟩
  refine ⟨hbij, hcdX.continuous, C, hC.le, fun z z' => ?_⟩
  have hdiff : Differentiable ℝ (Function.invFun (charFlow d b ν w (max t 0))) :=
    hcd.differentiable (by norm_num)
  have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := Function.invFun (charFlow d b ν w (max t 0))) (C := C) (fun x _ => hdiff x)
    (fun x _ => by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact (hder 1 le_rfl le_rfl x).2) (mem_univ z') (mem_univ z)
  exact this

end HRS.Whole.AppendixA.Phase2SA16Evolution
