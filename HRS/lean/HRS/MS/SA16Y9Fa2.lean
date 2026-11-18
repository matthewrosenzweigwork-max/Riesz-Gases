import HRS.MS.SA16Y9Fa1

/-!
# S.A.16 (SA16Y9) Fa2: the tie `sa16y9_adjoint_lp_stability : type_of% @adjoint_lp_stability`

Case split over `κc : LpCase`: `sub` (`sa16y9_sub_stability`, `sa16y9_sub_src`), `iso` and `hilbert` (`sa16y9_stab_of_class` with the dissipation/existence inputs of the
SA16Y5/SA16Y6C chains).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

set_option maxHeartbeats 3200000 in
theorem sa16y9_adjoint_lp_stability : type_of% @HRS.Whole.AppendixA.adjoint_lp_stability := by
  intro d hd s hs0 hsd m hm p hp κc MB Λ ΛV G₀ νbar T χ hχ
  cases κc with
  | sub =>
    by_cases hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)
    · obtain ⟨C, hC, H⟩ := sa16y9_sub_stability hd s hs0 hsd m hm p MB Λ ΛV G₀ νbar T χ hχ hsub
        (sa16y9_sub_src hd s hs0 hsd m p MB Λ ΛV G₀ νbar T hsub)
      exact ⟨C, hC, fun D₁ D₂ μ₁ μ₂ hD1 hD2 _ _ hM hV => H D₁ D₂ μ₁ μ₂ hD1 hD2 hM hV⟩
    · exact ⟨1, one_pos, fun D₁ D₂ μ₁ μ₂ hD1 hD2 hκ1 => absurd hκ1 hsub⟩
  | iso =>
    refine sa16y9_stab_of_class hd s hs0 hsd m hm p LpCase.iso MB Λ ΛV G₀ νbar T χ hχ
      (fun M : Matrix (Fin d) (Fin d) ℝ => ∃ lam : ℝ, 0 ≤ lam ∧ M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)))
      (fun M ⟨_, lam, hlam, hM⟩ => ⟨lam, hlam.le, hM⟩) (fun M ⟨h, _⟩ => h)
      (fun M ⟨lam, hlam, hM⟩ => ⟨lam, hlam, 0, by simp, by simp [hM]⟩)
      (fun m' h1 h2 h3 => sa16y5_Hd_iso hd hs0 h1 h2 h3 m' MB)
      (fun m' h1 h2 h3 => sa16y6c_Hd_iso hd hs0 h1 h2 h3 m' MB)
      (fun m' h1 => sa16y5f_Hex_iso hd hs0 hsd h1 m' MB)
  | hilbert =>
    by_cases hp2 : p = 2
    · refine sa16y9_stab_of_class hd s hs0 hsd m hm p LpCase.hilbert MB Λ ΛV G₀ νbar T χ hχ
        (fun M : Matrix (Fin d) (Fin d) ℝ => ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
          M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A)
        (fun M ⟨_, _, lam, hlam, A, hA, hM⟩ => ⟨lam, hlam, A, hA, hM⟩) (fun M ⟨h, _⟩ => h)
        (fun M h => h)
        (fun m' h1 h2 h3 => sa16y5_Hd_hilb hd hs0 h1 h2 h3 m' MB)
        (fun m' h1 h2 h3 => sa16y6c_Hd_hilb hd hs0 h1 h2 h3 m' MB)
        (fun m' h1 => sa16y5f_Hex_hilb hd hs0 hsd h1 hp2 m' MB)
    · exact ⟨1, one_pos, fun D₁ D₂ μ₁ μ₂ hD1 hD2 hκ1 => absurd hκ1.2.1 hp2⟩

end HRS.Whole.AppendixA.Phase2SA16R
