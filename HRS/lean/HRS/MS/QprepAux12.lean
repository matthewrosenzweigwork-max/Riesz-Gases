import HRS.MS.QprepAux11

/-!
# S4.6 packet A12: the uniform setup and `quadratic_preparation_static_proof`

`s46_setup`: one set of constants `(Cs, C, c, B_U, K_R, K_T)` for all `a ∈ [am,ap]`, `β ∈ [βm,βp]`, `γ ∈ [γm,γp]`.
`quadratic_preparation_static_proof`: copy of `S45.quadratic_static_field_proof` with the Gibbs law `Q_{N,γ}`
(`s46_P_eq`), the corrector at three temperatures (`thermal_corrector_proof`) and the constant
`K_R C_c + γm⁻¹ K_T C_c` (`γ⁻¹ ≤ γm⁻¹`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S46

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s46_setup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp γm γp : ℝ}
    (ham : 0 < am) (hβm : 0 < βm) (hγm : 0 < γm) (hap : am ≤ ap) (hβp : βm ≤ βp) (hγp : γm ≤ γp) :
    ∃ Cs C c BU KR KT : ℝ, 0 ≤ Cs ∧ 0 ≤ KR ∧ 0 ≤ KT ∧ ∀ a ∈ Set.Icc am ap, ∀ β ∈ Set.Icc βm βp,
      ∀ γ ∈ Set.Icc γm γp, S46Setup d s a β γ Cs C c BU KR KT := by
  obtain ⟨C, c, BU, hT⟩ := s46_thermal_data_unif hd hs0 hsd ham hβm hap hβp
  obtain ⟨Cs, hCs, hS⟩ := s46_static_all hd hs0 hsd ham hβm hγm hap hβp hγp
  obtain ⟨KR, hKR, hR⟩ := s46_R_bound hd hs0 hsd C Cs hCs
  obtain ⟨KT, hKT, hTb⟩ := s46_T_bound hd hs0 hsd Cs hCs
  refine ⟨Cs, C, c, BU, KR, KT, hCs, hKR, hKT, fun a ha β hβ γ hγ => ?_⟩
  exact ⟨hT a ha β hβ, hCs, hS a ha β hβ γ hγ, hKR,
    fun N hN _ hχ _ hB2 => hR (hT a ha β hβ) (hS a ha β hβ γ hγ) N hN hχ hB2, hKT,
    fun N hN _ hf _ hbd => hTb (hT a ha β hβ) (hS a ha β hβ γ hγ) N hN hf hbd⟩

end S46

end
