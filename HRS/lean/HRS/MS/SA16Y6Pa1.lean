import HRS.MS.SA16Y6Tc7
import HRS.MS.SA16Y5Pa1

/-!
# S.A.16 (SA16Y6) Pa1: the heat-composed nonlocal operator as a bounded operator on `W^{k,p}` at the boundary `s = d-1`

`sa16y6_Pa_exists` (`s = d-1`, `d ≥ 1`, `0 < a ≤ 1`, `p ≥ 2`): same statement as `sa16y5_Pa_exists` (which treats `d-1 < s < d`):
`∃ C`, for `|M_ij| ≤ MB`, smooth `μ` with `‖D^κ μ‖_∞ ≤ W` (`κ ≤ k+1`) there is a CLM `P_a : W^{k,p} → W^{k,p}`,
`‖P_a‖ ≤ C a^{-(s+2-d)/2} = C a^{-1/2}`, with `wrep (P_a (Jcc φ)) = g_a ⋆ eucNonlocal s M μ φ` a.e.  The proof uses the Calderón-Zygmund
bound for the Riesz transform instead of `L¹` kernels (`d = 1`, `s = 0` included).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Pa6
variable {d : ℕ}

theorem sa16y6_Pa_exists (hd : 1 ≤ d) {s : ℝ} (hs : s = (d : ℝ) - 1) (k : ℕ)
    (p : ℝ) [Fact (2 ≤ p)] (MB W : ℝ) (hMB : 0 ≤ MB) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ},
      ContDiff ℝ ∞ μ → (∀ κ ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ κ μ x‖ ≤ W) → ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      ∃ Pa : WmpSpace d k p →L[ℝ] WmpSpace d k p, ‖Pa‖ ≤ C * a ^ (-((s + 2 - d) / 2)) ∧
        ∀ φ : ccSub d, wrep d k p (Pa (sa16r_Jcc d k p φ)) =ᵐ[volume]
          sa16r_cv (sa16r_g d a) (HRS.MH.AdjointRd.eucNonlocal s M μ φ.1) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hexp : (s + 2 - (d : ℝ)) / 2 = 1 / 2 := by rw [hs]; ring
  obtain ⟨CJ, hCJ0, hCJ⟩ := sa16y6_Fam_pd_bound hd p hp2 k MB W hMB hW
  refine ⟨(Fintype.card (WIndex d k) : ℝ) * CJ, by positivity, ?_⟩
  intro M hM μ hμ hμb a ha ha1
  have hX0 : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  obtain ⟨T, hT, hTφ⟩ := sa16y5_ext_of_fun d k k p (fun φ => sa16y6_Fam d a M μ φ.1)
    (fun φ ψ => sa16y6_Fam_add hd ha M hμ φ.2 ψ.2)
    (fun c φ => sa16y6_Fam_smul hd ha M hμ φ.2 c)
    (fun φ => sa16y6_Fam_smooth hd ha M hμ φ.2) (c0 := CJ * a ^ (-(1 / 2 : ℝ)))
    (mul_nonneg hCJ0 hX0)
    (fun φ {j} hj idx => hCJ M hM hμ hμb ha ha1 φ hj idx)
  rw [hexp]
  refine ⟨T, by rw [mul_assoc]; exact hT, fun φ => ?_⟩
  filter_upwards [hTφ φ] with x hx
  rw [hx, sa16y6_Fam_eq hd hs ha M hμ φ.2]

end Pa6

end HRS.Whole.AppendixA.Phase2SA16R
