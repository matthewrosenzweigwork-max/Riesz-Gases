import HRS.Uniform.Q54cAux27

/-!
# Q54c, part 28: compatibility of the path data with the propagator
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.y_eq {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    (P.pd D μ).y t φ σ = lpFun (P.n : ℝ) (propagator D μ σ t φ) := by
  obtain ⟨h1, -, -⟩ := h.U_facts ht hφ hσ
  rw [h1]
  rfl

theorem Data.memSob_prop {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) {j : ℝ} (hj : j ≤ P.lev) :
    MemSobolev j (propagator D μ σ t φ) := by
  obtain ⟨-, -, hD⟩ := h.U_facts ht hφ hσ
  exact HRS.PDE.MFAdjoint.memSobolev_mono_idx hD.2 hj

theorem Data.w_eq {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    (P.pd D μ).w t φ = lpFun ((P.n : ℝ) + 2) (propagator D μ 0 t φ) := by
  obtain ⟨h1, -, -⟩ := h.U_facts ht hφ (σ := 0) ⟨le_rfl, ht.1⟩
  rw [h1, sub_zero]
  rfl

theorem Data.hw {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (z : NegSobolev d ((P.n : ℝ) + 2)) :
    inner ℝ z ((P.pd D μ).w t φ) = NegSobolev.eval z (propagator D μ 0 t φ) := by
  rw [h.w_eq ht hφ]
  exact (eval_lpFun z (h.memSob_prop ht hφ ⟨le_rfl, ht.1⟩ lev_ge_n2)).symm

end PdeSetup

end HRS.Uniform.Q54c
