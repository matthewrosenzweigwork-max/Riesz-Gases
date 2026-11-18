import HRS.MS.SA16Y4Nl2
import HRS.MS.SA16SEn11

/-!
# S.A.16 (SA16Y4) Nl3: compatible nonlocal operators of the mollified coefficient at levels `m` and `m+1`

`sa16y4_nl_pair`: for a `(m+3, Λ)`-regular density `μ` and `N : ℕ` there are `T1 : W^{m+1,p} → W^{m+1,p}` and
`T0 : W^{m,p} → W^{m,p}`, both with zeroth component `eucNonlocal s M (ρ_N ⋆ μ) φ` on `Jcc φ`, `ι T1 = T0 ι`, `‖T0‖ ≤ CG`,
`‖T1‖ ≤ CG1`, with `CG, CG1` independent of `M, μ, N` (given `MB, Λ`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nl3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y4_nl_pair (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ CG CG1 : ℝ, 0 < CG ∧ 0 < CG1 ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ → ∀ N : ℕ,
        ∃ (T1 : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p) (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p),
          ‖T0‖ ≤ CG ∧ ‖T1‖ ≤ CG1 ∧ (sa16r_iota d m p).comp T1 = T0.comp (sa16r_iota d m p) ∧
          (∀ φ : ccSub d, wrep d m p (T0 (sa16r_Jcc d m p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M (sa16q_mol N μ) φ.1) ∧
          (∀ φ : ccSub d, wrep d (m + 1) p (T1 (sa16r_Jcc d (m + 1) p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M (sa16q_mol N μ) φ.1) := by
  set W : ℝ := (d : ℝ) ^ (m + 3) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) with hW
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  obtain ⟨C0, hC0, h0⟩ := sa16y4_G_exists_smooth d m s p MB W hs0 hs2 hfar hW0
  obtain ⟨C1, hC1, h1⟩ := sa16y4_G_exists_smooth d (m + 1) s p MB W hs0 hs2 hfar hW0
  refine ⟨C0, C1, hC0, hC1, fun M hM μ hμ N => ?_⟩
  obtain ⟨hSB, hwt⟩ := sa16y4_mol_data3 hd hμ N
  obtain ⟨T0, hT0, hT0s⟩ := h0 M hM _ hSB (fun κ hκ x => hwt κ (by omega) x)
  obtain ⟨T1, hT1, hT1s⟩ := h1 M hM _ hSB (fun κ hκ x => hwt κ (by omega) x)
  exact ⟨T1, T0, hT0, hT1, sa16sz_nl_compat m hT1s hT0s, hT0s, hT1s⟩

end Nl3

end HRS.Whole.AppendixA.Phase2SA16R
