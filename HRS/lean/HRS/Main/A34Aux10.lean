import HRS.Main.A34Aux9

/-!
# Packet A34, helper 10: Proposition A.34 (i), quantitative, for `MainData`/`LimitCoeffs`
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

theorem a34_stat_main (s : ℝ) (Rg : Regime) (ν₀ MB Λ T Cin : ℝ) (VB : ℝ) (m m₀ : ℕ)
    (hm : 1 ≤ m) (hm₀ : m₀ ≤ m) (hms : mStar d ≤ m + 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (L : LimitCoeffs d), CoeffConvergence S L Rg ν₀ MB Λ VB (m + 2) m →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η : Ω → (Torus d → ℝ) → ℝ), XHyp P η m₀ Cin →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ φ : Torus d → ℝ, MemSobolev ((m + 2 : ℕ) : ℝ) φ →
        Continuous φ → ∀ N : ℕ, 1 ≤ N →
        wassersteinE 1
          (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ) P η)
          (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ) P η) ≤
        ENNReal.ofReal (C * sobolevNorm ((m + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L m N + Real.sqrt (S.coeffDiscrepancy L m N))) := by
  by_cases hg : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨1, one_pos, fun S hs _ => absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hg⟩
  obtain ⟨hd, hs0, hsd⟩ := hg
  obtain ⟨C, hC, h⟩ := a34_stat_abstract hd s hs0 hsd Rg ν₀ MB Λ VB T Cin m m₀ hm hm₀ hms
  refine ⟨C, hC, fun S hs hT L hcoef Ω _ P _ η hη t ht φ hφ hφc N hN => ?_⟩
  subst hs hT
  have hAN := hcoef.seq_adjoint N hN
  have hAL := hcoef.limit_adjoint
  obtain ⟨hΔ0, hρΔ, hβΔ, hqΔ, hAΔ⟩ := a34_delta_facts S L m N Rg ν₀ MB Λ VB hAN hAL
  have hq := a34_qScale_bounds (N := N) (by omega) (S.hκ N) (S.hinvβ N)
  have hA1 := a34_Ascale_abs_le (N := N) (κ := S.κ N) (invβ := S.invβ N) (S.hκ N)
  exact h (S.dyn N) (L.dyn S) (S.ρ N) L.ρ (S.AN N) L.A (S.qN N) L.invβstar
    (S.coeffDiscrepancy L m N) hAN hAL rfl rfl hΔ0 hρΔ hβΔ hq.1 hq.2 L.hinvβstar hqΔ hA1 hAΔ P η hη
    t ht φ hφ hφc

end HRS.A34
