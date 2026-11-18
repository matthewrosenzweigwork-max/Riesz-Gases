import HRS.MS.SA16Y9Ip1

/-!
# S.A.16 (SA16Y9) Dm1: level monotonicity of the coefficient data (stability, G2d, part 2)

`sa16y9_data_mono`: `AdjointRdData s m …` implies `AdjointRdData s m' …` for `m' ≤ m` (a proved version of the unproved `data_mono`
of `AdjointRdSpec`); `sa16y9_regDensity_mono`: `IsRegularDensityW r Λ ρ → IsRegularDensityW r' Λ ρ` for `r' ≤ r`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

section Dm1
variable {d : ℕ}

lemma sa16y9_cbNorm_mono {r r' : ℕ} (hr : r' ≤ r) (ρ : Euc d → ℝ) : cbNorm r' ρ ≤ cbNorm r ρ := by
  unfold cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun j _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

lemma sa16y9_weightedSupE_mono {r r' : ℕ} (hr : r' ≤ r) (L : ℝ) (ρ : Euc d → ℝ) :
    weightedSupE r' L ρ ≤ weightedSupE r L ρ := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  exact le_iSup₂_of_le (⟨(j : ℕ), by omega⟩ : Fin (r + 1)) i (le_iSup_of_le x le_rfl)

lemma sa16y9_regDensity_mono {r r' : ℕ} (hr : r' ≤ r) {Λ : ℝ} {ρ : Euc d → ℝ} (h : IsRegularDensityW r Λ ρ) :
    IsRegularDensityW r' Λ ρ := by
  obtain ⟨h1, ⟨-, h2⟩, h3⟩ := h
  refine ⟨h1.of_le (by exact_mod_cast hr), ⟨h1.of_le (by exact_mod_cast hr), fun j hj => h2 j (hj.trans hr)⟩, ?_⟩
  refine le_trans ?_ h3
  exact add_le_add (ENNReal.ofReal_le_ofReal (sa16y9_cbNorm_mono hr ρ)) (sa16y9_weightedSupE_mono hr _ ρ)

theorem sa16y9_data_mono {s : ℝ} {m m' : ℕ} (h : m' ≤ m) {MB Λ ΛV G₀ νbar T : ℝ} {D : WholeDyn d}
    {μ : ℝ → Euc d → ℝ} (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) :
    AdjointRdData s m' MB Λ ΛV G₀ νbar D T μ := by
  refine ⟨hD.hs, hD.hM, ?_, ⟨hD.hμ.prob, ?_, hD.hμ.cont⟩, hD.hT, hD.hν⟩
  · obtain ⟨h1, h2, h3⟩ := hD.hV
    exact ⟨h1, fun j hj hjm x => h2 j hj (by omega) x, h3⟩
  · obtain ⟨hr, hf⟩ := hD.hμ.regular
    refine ⟨fun t ht => ?_, hf⟩
    obtain ⟨hcb, hfin, hsum⟩ := hr t ht
    refine ⟨⟨hcb.1.of_le (by exact_mod_cast (by omega : m' + 3 ≤ m + 3)),
      fun j hj => hcb.2 j (by omega)⟩, ?_, ?_⟩
    · exact lt_of_le_of_lt (sa16y9_weightedSupE_mono (by omega) _ _) hfin
    · refine le_trans (add_le_add (sa16y9_cbNorm_mono (by omega) _)
        (ENNReal.toReal_mono hfin.ne (sa16y9_weightedSupE_mono (by omega) _ _))) hsum

end Dm1

end HRS.Whole.AppendixA.Phase2SA16R
