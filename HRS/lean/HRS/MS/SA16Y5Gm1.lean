import HRS.MS.SA16Y5Cv5
import HRS.MS.SA16RHeat13
import HRS.MS.SA16SSt1

/-!
# S.A.16 (SA16Y5) Gm1: the gain operator on a closed-jet element with bounded continuous zeroth component (K3 helper)

`sa16y5_wrep_eLpNorm_le`: `‖wrep G‖_p ≤ ‖G‖`.
`sa16y5_Gam_wrep`: if `wrep y = F` a.e. with `F` continuous and bounded then `wrep (Γ_a y) = g_a ⋆ F` a.e.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Gm1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y5_wrep_sub (k : ℕ) (G H : WmpSpace d k p) :
    wrep d k p (G - H) =ᵐ[volume] fun x => wrep d k p G x - wrep d k p H x := by
  have h1 := sa16r_wrep_add d k p G (-H)
  have h2 := sa16r_wrep_smul d k p (-1) H
  rw [sub_eq_add_neg]
  filter_upwards [h1, h2] with x hx hy
  rw [hx]
  have : (-H : WmpSpace d k p) = (-1 : ℝ) • H := (neg_one_smul ℝ H).symm
  rw [this, hy]
  ring

lemma sa16y5_wrep_eLpNorm_le (k : ℕ) (G : WmpSpace d k p) :
    eLpNorm (wrep d k p G) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ‖G‖ := by
  have hm : AEStronglyMeasurable (wrep d k p G) volume := (sa16sx_loc k G).aestronglyMeasurable
  have h1 : eLpNorm (wrep d k p G) (ENNReal.ofReal p) volume ≤
      eLpNorm ((G : WLp d k p) : Euc d → (WIndex d k → ℝ)) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono_ae hm (Eventually.of_forall fun x => ?_)
    simp only [wrep]
    rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    exact norm_le_pi_norm (((G : WLp d k p) : Euc d → (WIndex d k → ℝ)) x) (wZero d k)
  refine h1.trans (le_of_eq ?_)
  have : ‖G‖ = ‖(G : WLp d k p)‖ := rfl
  rw [this, Lp.norm_def, ENNReal.ofReal_toReal ((Lp.memLp (G : WLp d k p)).eLpNorm_lt_top.ne)]

end Gm1

end HRS.Whole.AppendixA.Phase2SA16R
