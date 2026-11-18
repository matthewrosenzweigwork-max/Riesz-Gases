import HRS.MS.WadAux88
import HRS.MS.WadAux70

/-!
# S8.3, packet S8E-4, part 5: clause (3) of the frozen `weighted_adjoint_decay` for `j ≤ 1`

`s8e_clause3_le_one`: for every `U` with `IsWeightedSemigroup`, `j ≤ 1` and `T ≥ 0` there is `K` with
`U_t f ∈ C_M^j` and `‖U_t f‖_{C_M^j} ≤ K ‖f‖_{C_M^j}` for `t ∈ [0,T]`, `f ∈ C_M^j` (the fourth conjunct of the
frozen statement for `j ∈ {0,1}`; `j = 0` is the `bdd` field, `j = 1` is `s8e_clause3_one`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_clause3_le_one (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M)
    {U : ℝ → (Euc d → ℝ) → Euc d → ℝ}
    (hU : IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U) {j : ℕ} (hj : j ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ f : Euc d → ℝ, MemCMj M j f →
      MemCMj M j (U t f) ∧ weightedSupE j (-M) (U t f) ≤ ENNReal.ofReal K * weightedSupE j (-M) f := by
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · obtain ⟨K, hK⟩ := hU.bdd T hT
    refine ⟨K, fun t ht f hf => ?_⟩
    have hfM : MemCM M f := by
      refine ⟨hf.1.continuous, ?_⟩
      have := hf.2 0 le_rfl (fun i => i.elim0)
      simpa [partialDeriv] using this
    have hm := hU.maps t ht.1 f hfM
    refine ⟨⟨contDiff_zero.2 hm.1, fun i hi idx => ?_⟩, hK t ht f hfM⟩
    have hi0 : i = 0 := by omega
    subst hi0
    simpa [partialDeriv] using hm.2
  · have H : S85Hyp d a β (T + 1) M ρβ := ⟨hd, ha, hβ, by linarith, hMpos.le, hρ⟩
    obtain ⟨K, hK1, hK⟩ := s8e_clause3_one H hMpos
    refine ⟨K, fun t ht f hf => ?_⟩
    have hfM : MemCM M f := s8e_memCM_of_j hf
    rw [s85_semigroup_unique hd ha hβ hρ hMpos hU ht.1 hfM]
    exact hK ht.1 (ht.2.trans (by linarith)) hf

end HRS.MS.Wad
