import HRS.MP.RdInit
import HRS.MP.RdPropAssemble

/-!
# Closing `path_initial_modulus_rd` (S.A.23, particle clause on `ℝ^d`)

The frozen statement follows from `RdInit.path_initial_modulus_rd_of_increment` (conditional on the increment bound
`IncrementBoundRd` with a constant `C₁`) and `RdProp.rpa_core` (S.A.22, which supplies `C₁` before `S`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.RdInitClose
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem path_initial_modulus_rd_proof (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kadj Cw Cin : ℝ) (m₀ : ℕ) (hm₀' : m₀ ≤ mStar d) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) →
      fd.Holds S ν₀ → PDE.MatBound MB S.M → MeanFieldRegularityRd S (fd.Gamma + 5) Λ →
      VHypRd (fd.Gamma + 5) ΛV G₀ S.V → PathAdjointInput S fd.Gamma m₀ Kadj Cw →
      ∀ (R : ∀ N, RealizationRd d N) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Euc d → ℝ)),
        InitialFluctuationRd S R χ m₀ Cin ε Ψ →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ)),
        IsInitReprRd S R (fd.Gamma + 2) Iq Jq →
        (∀ N : ℕ, 1 ≤ N → ∀ s' ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
          ∫⁻ ζ, ‖Iq N t ζ - Iq N s' ζ‖ₑ ^ 2 ∂(R N).P + ∫⁻ ζ, ‖Jq N t ζ - Jq N s' ζ‖ₑ ^ 2 ∂(R N).P ≤
            ENNReal.ofReal (C * |t - s'| ^ 2)) ∧
        (∃ Zc, ContVersionTight T (fun N => (R N).P) (fun N t ζ => Iq N t ζ) Zc) ∧
        (∃ Zc, ContVersionTight T (fun N => (R N).P) (fun N t ζ => Jq N t ζ) Zc) := by
  obtain ⟨C₁, hC₁⟩ := HRS.MP.RdProp.rpa_core s fd ν₀ MB Λ ΛV G₀ νbar T Kadj Cw m₀ hm₀'
  obtain ⟨C, hC⟩ := HRS.MP.RdInit.path_initial_modulus_rd_of_increment s fd T Kadj Cin C₁ m₀ χ hχ
  refine ⟨C, fun S hs hT hν hH hMB hMF hV hP R ε Ψ hinit εf Iemp I _ _ Iq Jq hrepr => ?_⟩
  exact hC S hT hP.adjoint (fun N hN => (hC₁ S hs hT hν hH hMB hMF hV hP).1 N hN |>.1) R ε Ψ hinit Iq Jq hrepr

example := (@path_initial_modulus_rd_proof :
  type_of% @HRS.Whole.AppendixALemmas.path_initial_modulus_rd)

end HRS.MP.RdInitClose
