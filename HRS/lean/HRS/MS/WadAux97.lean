import HRS.MS.WadAux96

/-!
# S8.3, packet S8E-6, part 1: clause (2b) of the frozen statement for `j ≤ 1`

`s8e_clause2b_le_one`: for every `U` with `IsWeightedSemigroup` and `j ≤ 1` there are `C_j, c > 0` with
`U_tP_μ f ∈ C_M^j` and `‖U_tP_μ f‖_{C_M^j} ≤ C_j e^{-ct} ‖f‖_{C_M}` for `t ≥ 1`, `f ∈ C_M` (`j = 0` is `s8d_clause2a`,
`j = 1` is `s8d_clause2b_one`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_clause2b_le_one (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) {j : ℕ} (hj : j ≤ 1) :
    ∃ Cj c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ f : Euc d → ℝ, MemCM M f →
      MemCMj M j (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ∧
      weightedSupE j (-M) (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
        ENNReal.ofReal (Cj * Real.exp (-c * t)) * weightedSupE 0 (-M) f := by
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · obtain ⟨Cd, c, hc, h⟩ := s8d_clause2a hd ha hβ hρ hMpos hU
    refine ⟨Cd, c, hc, fun t ht f hf => ⟨?_, h t ht f hf⟩⟩
    have hm := hU.maps t (by linarith) (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)
      (s8d_memCM_projMean hMpos hf)
    refine ⟨contDiff_zero.2 hm.1, fun i hi idx => ?_⟩
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [partialDeriv] using hm.2
  · obtain ⟨C1, c, hc, h⟩ := s8d_clause2b_one hd ha hβ hρ hMpos
    refine ⟨C1, c, hc, fun t ht f hf => ?_⟩
    rw [s85_semigroup_unique hd ha hβ hρ hMpos hU (by linarith) (s8d_memCM_projMean hMpos hf)]
    exact h ht hf

end HRS.MS.Wad
