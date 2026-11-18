import HRS.MH.AdjointRdDefs

/-!
# S.A.12 X5: definitions for the paired (stability) periodic estimate

`sa12x5_src` is the source of the difference `G = F₁ - F₂` of two periodic solutions with coefficients
`(ν₁, μ₁, b₁)` and `(ν₂, μ₂, b₂)`: `∂_τ G = ν₁ΔG + b₁·∇G - 𝒢_{μ₁}G + S` with
`S = (ν₁-ν₂)ΔF₂ + (b₁-b₂)·∇F₂ - (𝒢_{μ₁}F₂ - 𝒢_{μ₂}F₂)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- The source of the difference of two periodic solutions. -/
def sa12x5_src (L : ℝ) (γ : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν₁ ν₂ : ℝ)
    (μ₁ μ₂ : ℝ → Euc d → ℝ) (b₁ b₂ : ℝ → Euc d → Euc d) (F₂ : ℝ → Euc d → ℝ) :
    ℝ → Euc d → ℝ := fun τ x =>
  (ν₁ - ν₂) * Laplacian.laplacian (F₂ τ) x + inner ℝ (b₁ τ x - b₂ τ x) (gradient (F₂ τ) x) -
    (perNonlocal L γ M (μ₁ τ) (F₂ τ) x - perNonlocal L γ M (μ₂ τ) (F₂ τ) x)

end HRS.MH.AdjointRd.Phase2SA12X5
