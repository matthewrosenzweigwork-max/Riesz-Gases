import HRS.MS.SA16ZE6
import HRS.MS.LpDissLimit

/-!
# S.A.16 (SA16Z) E7: measurability of the error and the Young bound for the error pairing
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section E7
variable {d : ℕ} {s : ℝ}

lemma sa16z_T_cont (hd : 1 ≤ d) (hθ1 : 1 < s + 2 - d) (hθ2 : s + 2 - (d : ℝ) < 2) {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) (cA cs : ℝ) (l : Fin d) (j : ℕ) (idx : Fin j → Fin d) :
    Continuous (fun x => cA * (sa16z_dm μ l x * sa16z_pv d (s + 2 - d) l (partialDeriv idx φ) x) -
      cs * sa16z_Q j idx l (fun a κ => sa16z_dm μ a x * sa16z_pv d (s + 2 - d) l (partialDeriv κ φ) x)) := by
  have hdm : ∀ a : Fin d, Continuous (sa16z_dm μ a) := fun a => (sa16z_dm_smooth hμ a).continuous
  refine (continuous_const.mul ((hdm l).mul (sa16z_pv_cont hd hθ1 hθ2 hφ l idx))).sub
    (continuous_const.mul ?_)
  cases j with
  | zero => simp only [sa16z_Q]; exact continuous_const
  | succ n =>
    simp only [sa16z_Q]
    exact continuous_finsetSum _ fun q _ => (hdm _).mul (sa16z_pv_cont hd hθ1 hθ2 hφ l _)

lemma sa16z_Err_aesm (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {c cθ : ℝ} {μ φ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ)
    (hP : ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ x : Euc d,
      sa16z_P s μ ψ x = -c * fracLap d (s + 2 - d) (fun y => μ y * ψ y) x +
        HRS.CZ.Hls.hlsg_c s * ∑ i : Fin d, sa16z_pv d (s + 2 - d) i (fun y => sa16z_dm μ i y * ψ y) x)
    (j : ℕ) (idx : Fin j → Fin d) :
    AEStronglyMeasurable (fun x => sa16z_Err s c cθ μ φ j idx x) volume := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hθ0 : 0 < s + 2 - (d : ℝ) := by linarith
  have hfl := sa16bd_fracLap_aesm hd hθ0 hθ2 (sa16z_Wt hφ j idx)
  have hg : AEStronglyMeasurable (fun x => partialDeriv idx (sa16z_P s μ φ) x -
      (-c * (μ x * fracLap d (s + 2 - d) (partialDeriv idx φ) x) +
        ∑ l : Fin d, ((HRS.CZ.Hls.hlsg_c s - c * cθ) * (sa16z_dm μ l x * sa16z_pv d (s + 2 - d) l (partialDeriv idx φ) x) -
          HRS.CZ.Hls.hlsg_c s * sa16z_Q j idx l (fun a κ => sa16z_dm μ a x *
            sa16z_pv d (s + 2 - d) l (partialDeriv κ φ) x)))) volume := by
    refine (sa16j_pd_smooth (sa16z_P_smooth hs0 hsd hμ hφ) idx).continuous.aestronglyMeasurable.sub ?_
    refine AEStronglyMeasurable.add ?_ ?_
    · exact (aestronglyMeasurable_const.mul (hμ.continuous.aestronglyMeasurable.mul hfl))
    · exact (continuous_finsetSum _ fun l _ => sa16z_T_cont hd hθ1 hθ2 hμ hφ _ _ l j idx).aestronglyMeasurable
  refine hg.congr (Eventually.of_forall fun x => ?_)
  have := sa16z_decomp hd hs0 hsd (cθ := cθ) hμ hφ hP j idx x
  simp only
  linarith

end E7

end HRS.Whole.AppendixA.Phase2SA16R
