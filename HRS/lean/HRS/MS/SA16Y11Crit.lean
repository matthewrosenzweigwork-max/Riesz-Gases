import HRS.MS.SA16Y9Cc1
import HRS.MS.SA16Y11Co3c
import HRS.MS.SA16Y11Iso

/-!
# S.A.16 (SA16Y11) Crit: `Sa16CritSrc` (`SA16Y9Cc1`), the source bound required in the critical regime `s = d-1` (Calderon-Zygmund order-one operator)

(the pipeline copy `sa16y6c_approx3` uses the same `sa16y5_NInt` / `sa16y5_Kint`, with the operator from `sa16y6c_G_smooth`).
`sa16y11_critSrc : Sa16CritSrc ...` is proved from `sa16y11c_src_of_data`, `sa16y11_bcInt_bdd`, `sa16y4_drift_const`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Crit
variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y11_critSrc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (MB Λ ΛV G₀ νbar T : ℝ) (MCls : Matrix (Fin d) (Fin d) ℝ → Prop) :
    Sa16CritSrc d s m p MB Λ ΛV G₀ νbar T MCls := by
  intro hs1 hθ0 hfar
  have hsd : s < d := by linarith
  obtain ⟨Ce, hCe, H⟩ := sa16y11c_src_of_data d m hd s p MB Λ ΛV G₀ νbar T hs0 hs1 hfar
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd (m + 2) MB Λ ΛV G₀
  obtain ⟨B', hB'⟩ := sa16y11_bcInt_bdd d m hA0 hL0
  obtain ⟨-, ⟨Cj, hCj0, hCj⟩, -, -⟩ := closed_jet_energy_calculus d m p
  refine ⟨Ce, hCe.le, fun D₁ D₂ μ₁ μ₂ hD1 hD2 hMC hM hV δ hδ hcoef t ht n σ hσ v => ?_⟩
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hb1 := hB' t ht.1 (fun r => meanFieldDriftW D₁ (μ₁ r))
    (fun r hr => by
      obtain ⟨h1, h2, h3⟩ := hbc νbar T D₁ μ₁ hD1 r (htT r hr)
      exact ⟨h1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 2)), h2,
        fun j hj1 hj2 x => h3 j hj1 (by omega) x⟩) (n + 1) (Nat.succ_pos n) σ hσ
  have hb2 := hB' t ht.1 (fun r => meanFieldDriftW D₂ (μ₂ r))
    (fun r hr => by
      obtain ⟨h1, h2, h3⟩ := hbc νbar T D₂ μ₂ hD2 r (htT r hr)
      exact ⟨h1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 2)), h2,
        fun j hj1 hj2 x => h3 j hj1 (by omega) x⟩) (n + 1) (Nat.succ_pos n) σ hσ
  have h := H D₁ D₂ μ₁ μ₂ hD1 hD2 hM hV δ hδ hcoef t ht (n + 1) (Nat.succ_pos n) σ hσ _ _ hb1 hb2
    (D₁.invβ) (D₂.invβ) rfl v
  have e : (D₁.invβ - D₂.invβ) • sa16so_Lap d m p v +
      sa16r_iota d m p ((sa16y5_Kint d m (n + 1) p s D₁.M t μ₁ (fun r => meanFieldDriftW D₁ (μ₁ r)) σ -
        sa16y5_Kint d m (n + 1) p s D₂.M t μ₂ (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v) =
      (D₁.invβ - D₂.invβ) • sa16so_Lap d m p v +
          sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
            sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v) -
          sa16r_iota d m p ((sa16y5_NInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y5_NInt d m (n + 1) p s D₂.M t μ₂ σ) v) := by
    unfold sa16y5_Kint
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [e] at h
  exact ((hCj _).1).trans h
end Crit

end HRS.Whole.AppendixA.Phase2SA16R

end
