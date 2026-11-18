import HRS.MS.SA16Y10Nl0
import HRS.MS.SA16Y4Nl1
import HRS.MS.SA16SEn11

/-!
# S.A.16 (SA16Y10) Nl2: the nonlocal difference operator for `s ≤ d-2`, linear in the weight
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA MeasureTheory Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ}

theorem sa16y10_nl_diff_sub (d m : ℕ) (s p MB : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ a : Euc d → ℝ, sa16q_SB a →
      ∀ δ : ℝ, 0 ≤ δ → (∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ δ * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
        ∃ T : WmpSpace d (m + 2) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ K * δ ∧ SA16NlRep d m p s M T a := by
  obtain ⟨C, hC, h⟩ := sa16y4_G_exists_smooth d m s p MB 1 hs0 hs2 hfar zero_le_one
  refine ⟨C * ‖sa16sz_iota2 d m p‖, by positivity, fun M hM a ha δ hδ hdec => ?_⟩
  refine sa16y10_lin_abstract (m + 2) (-((d + 3 : ℕ) : ℝ)) (fun T a => SA16NlRep d m p s M T a) sa16q_SB
    (fun a h => h.1) (fun a c h => sa16y10_SB_smul h c) (fun T a c h => sa16y10_rep_smul h c) _ ?_ a ha δ hδ hdec
  intro a ha hd1
  obtain ⟨T0, hT0, hrep0⟩ := h M hM a ha (fun κ hκ x => hd1 κ (by omega) x)
  refine ⟨T0.comp (sa16sz_iota2 d m p), (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hT0 (norm_nonneg _)), fun φ => ?_⟩
  show wrep d m p (T0 (sa16sz_iota2 d m p (sa16r_Jcc d (m + 2) p φ))) =ᵐ[volume] _
  rw [sa16sz_iota2_Jcc]
  exact hrep0 φ

end HRS.Whole.AppendixA.Phase2SA16R

end
