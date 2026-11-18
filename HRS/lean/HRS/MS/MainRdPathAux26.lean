import HRS.MS.MainRdPathAux25

/-!
# S.A.9: `main_rd_path_proof`

`main_rd_path_proof` has exactly the type of the frozen statement `HRS.Whole.AppendixA.main_rd_path`.
Route: `sa9_coreK` (representatives and tightness), `sa9_fidi` (finite-dimensional convergence for Schwartz families,
with the fixed-time initial vector extracted from `EmpiricalInitialVectorConverges` with the explicit a.e.-measurability
premise), `sa9_assemble` (tight + finite-dimensional marginals imply weak convergence on `C([0,T]; H^{-(Γ+2)})`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

theorem main_rd_path_proof : type_of% @HRS.Whole.AppendixA.main_rd_path := by
  intro d s fd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
  obtain ⟨C1, h1⟩ := sa9_coreK s fd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
  obtain ⟨C2, h2⟩ := sa9_fidi s fd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
  refine ⟨max C1 C2, fun C₀ hC₀ S hs hT hinv hH R 𝔈 hS m₂ hm₂0 hm₂ m₀ ε hinit εf Iemp I hTIF hdist L
    hHA hcoef K hW hFA hAdjP hAdjL hStab hsm hfix hemp => ?_⟩
  have hConc := h1 C₀ (le_trans (le_max_left _ _) hC₀) S hs hT hinv hH R 𝔈 hS m₂ hm₂0 hm₂ m₀ ε hinit εf
    Iemp I hTIF hdist L hcoef.tendsto K hW.particles hFA hAdjP hAdjL hStab hsm
  refine ⟨hConc.1, ?_⟩
  intro νη hνη Ω' _ P' _ η₀ Y hlaw hη₀m hYc hYm hdual Ξ hΞ
  refine sa9_assemble hConc P' Y hYc hYm ?_ Ξ (fun N hN => (hΞ N hN).1) (fun N hN => (hΞ N hN).2)
  intro p ts φ hts hφ
  have hts' : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T := fun a => hT ▸ hts a
  exact h2 C₀ (le_trans (le_max_right _ _) hC₀) S hs hT hinv hH R 𝔈 hS m₂ hm₂0 hm₂ p ts φ hts' hφ m₀ ε
    hinit εf Iemp I hTIF hdist L hcoef hFA hAdjL hStab hsm νη hνη P' η₀ Y hlaw hη₀m
    (hemp p ts φ hts' hφ νη hνη P' η₀ hlaw hη₀m) (hT ▸ hdual)

end HRS.MS.MainRdPath

example := (@HRS.MS.MainRdPath.main_rd_path_proof : type_of% @HRS.Whole.AppendixA.main_rd_path)
