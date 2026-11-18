import HRS.MS.SA16Y10Nl2
import HRS.MS.SA16Y4Nl3
import HRS.MS.SA16Y4Nc8

/-!
# S.A.16 (SA16Y10) Nd1: node-wise difference of the mollified nonlocal operators (`s ≤ d-2`)

`sa16y10_node_diff_sub`: for regular densities `μ₁, μ₂` with `‖D^κ(μ₁-μ₂)‖ ≤ δ (1+|x|)^{-(d+3)}` (`κ ≤ m+2`),
`‖(G(mol N μ₁) - G(mol N μ₂)) ∘ ι²‖_{W^{m+2}→W^m} ≤ K δ`, `G = sa16so_G`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA MeasureTheory Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ}

lemma sa16y10_mol_sub (n : ℕ) {f g : Euc d → ℝ} (hf : Continuous f) (hg : Continuous g) {B : ℝ}
    (hfB : ∀ y, |f y| ≤ B) (hgB : ∀ y, |g y| ≤ B) :
    sa16q_mol n (fun y => f y - g y) = fun x => sa16q_mol n f x - sa16q_mol n g x := by
  funext x
  have hρc : Continuous (sa16y_rho d n) := sa16y_rho_smooth n |>.continuous
  have hint : ∀ h : Euc d → ℝ, Continuous h → (∀ y, |h y| ≤ B) →
      Integrable (fun z => sa16y_rho d n z * h (x - z)) := by
    intro h hc hB'
    refine Integrable.mono' ((sa16y_rho_integrable n).mul_const B)
      (hρc.aestronglyMeasurable.mul (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sa16y_rho_nonneg n z), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB' _) (sa16y_rho_nonneg n z)
  show ∫ z, sa16y_rho d n z * (f (x - z) - g (x - z)) = (∫ z, sa16y_rho d n z * f (x - z)) -
    ∫ z, sa16y_rho d n z * g (x - z)
  rw [← integral_sub (hint f hf hfB) (hint g hg hgB)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  ring

end HRS.Whole.AppendixA.Phase2SA16R

end
