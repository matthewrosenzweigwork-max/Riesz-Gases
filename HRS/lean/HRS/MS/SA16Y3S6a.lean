import HRS.MS.SA16Y3S4
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 (SA16Y3) S6a: the `IsLpSolutionRd` fields `wcont` and `bounded` for a weakly continuous bounded path in `WmpSpace`

For `G0 : ℝ → WmpSpace d m p` with `ℓ ∘ G0` continuous on `[0,t]` for every `ℓ` and `‖G0 τ‖ ≤ Bg`, the function
`F τ := wrep (G0 τ)` satisfies `IsWmpWeaklyContinuous m p t F` (`sa16y3_wcont_of_path`), `wNormE m p (F τ) ≤ ofReal ‖G0 τ‖`
(`sa16y3_wNormE_le`) and the `bounded` field of `IsLpSolutionRd` (`sa16y3_bounded_of_path`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section S6a
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y3_wNormE_le {m : ℕ} (G : WmpSpace d m p) :
    wNormE m p (fun x => wrep d m p G x) ≤ ENNReal.ofReal ‖G‖ :=
  iInf₂_le G (Eventually.of_forall fun x => rfl)

theorem sa16y3_wcont_of_path {m : ℕ} {t Bg : ℝ} (G0 : ℝ → WmpSpace d m p)
    (hc : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G0 τ)) (Icc (0 : ℝ) t)) :
    IsWmpWeaklyContinuous m p t (fun τ x => wrep d m p (G0 τ) x) := by
  refine ⟨fun τ _ => (sa16y3_wNormE_le (G0 τ)).trans_lt ENNReal.ofReal_lt_top, fun G hG ℓ => ?_⟩
  refine (hc ℓ).congr (fun τ hτ => ?_)
  have : G τ = G0 τ := sa16r_wrep_inj d m p _ _ (hG τ hτ)
  rw [this]

theorem sa16y3_bounded_of_path {m : ℕ} {t Bg : ℝ} (G0 : ℝ → WmpSpace d m p)
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ‖G0 τ‖ ≤ Bg) :
    ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (fun x => wrep d m p (G0 τ) x) ≤ ENNReal.ofReal B :=
  ⟨Bg, fun τ hτ => (sa16y3_wNormE_le (G0 τ)).trans (ENNReal.ofReal_le_ofReal (hB τ hτ))⟩

end S6a

end HRS.Whole.AppendixA.Phase2SA16R
