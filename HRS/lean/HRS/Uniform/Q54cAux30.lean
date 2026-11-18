import HRS.Uniform.Q54cAux29

/-!
# Q54c, part 30: comparison of the path data of two adjoint dynamics
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

variable {P : PdeSetup d} (cc : P.CmpConst) {D₁ D₂ : DynData d} {ν₀ : ℝ} {μ₁ μ₂ : ℝ → Torus d → ℝ}
  (h₁ : P.Data D₁ ν₀ μ₁) (h₂ : P.Data D₂ ν₀ μ₂) (hM : D₁.M = D₂.M) (hV : D₁.V = D₂.V) {δ : ℝ}
  (hδ : ∀ r ∈ Set.Icc 0 P.T, Torus.cbNorm (P.n + 4) (μ₁ r - μ₂ r) ≤ δ)

theorem lev_eq (P : PdeSetup d) : P.lev = (P.n : ℝ) + 4 := by unfold PdeSetup.lev; push_cast; ring

include cc h₁ h₂ hM hV hδ

/-- hs-norm comparison of the two flows (at level `n+2`). -/
theorem Data.cmp_flow {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) :
    HRS.PDE.hsNorm ((P.n : ℝ) + 2) (P.flow D₁ μ₁ t φ τ - P.flow D₂ μ₂ t φ τ) ≤
      cc.Cst * (|D₁.invβ - D₂.invβ| + δ) * sobolevNorm ((P.n : ℝ) + 4) φ := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  have h := cc.stab D₁ D₂ ν₀ μ₁ μ₂ h₁.hA h₂.hA hM hV δ hδ (coeffOf φ) (h₁.memHsφ hD) t ht τ hτ
  have hms : MemSobolev P.lev φ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ _
  rw [← HRS.PDE.ClassicalPart.sobolevNorm_eq_hsNorm hms] at h
  have e : sobolevNorm P.lev φ = sobolevNorm ((P.n : ℝ) + 4) φ := by rw [lev_eq]
  rw [e] at h
  exact h

end PdeSetup

end HRS.Uniform.Q54c
