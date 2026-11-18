import HRS.Energy.Commutator.Renorm
import HRS.Energy.Commutator.NearField

/-!
# Lipschitz-only regime `d - 2 ≤ s < d`: assembly (packet CM-S5)

`super_core` (Serfaty smearing, `Renorm.lean`) bounds `|Comm_N|` by
`C L (F_N + logPart + N⁻² ∑ selfExcess(r_i) + a_N^Λ)`; `nearField_control` (`NearField.lean`) bounds
the self-energy sum by `C₃ (F_N + o_N(C₀'))`.  Choosing `C₀ = C₃ C₀' + K` closes the estimate.
This file is **proved** modulo those two statements.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- **Regime `d - 2 ≤ s < d`**: `|Comm_N(v)| ≤ C L (F_N + o_N)` for `L`-Lipschitz `v`
(no fractional norm).  `C₀, C` depend only on `d, s`. -/
theorem commutator_estimate_super (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hs : (d : ℝ) - 2 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨C₁, K, hC₁, hK, hcore⟩ := super_core hd hs0 hs hsd
  obtain ⟨C₀', C₃, hC₀', hC₃, hNF⟩ := nearField_control hd hs0 hsd
  refine ⟨C₃ * C₀' + K, C₁ * (1 + C₃), by positivity, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX L v hL hv
  have h1 := hcore Λ hΛ N hN ρ hρ hρΛ X hX L v hL hv
  have h2 := hNF Λ hΛ N hN ρ hρ hρΛ X hX
  have ha := aNΛ_nonneg d s Λ N (by linarith)
  rw [oNΛ_eq] at h2 ⊢
  set F := rieszEnergy d s X (withDensityReal ρ) with hF
  set S := (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d s Λ N (smearRadius Λ X i) with hS
  set a := aNΛ d s Λ N with ha_def
  set lp := logPart d s Λ N with hlp
  have hT : F + lp + S + K * a ≤ (1 + C₃) * (F + (lp + (C₃ * C₀' + K) * a)) := by
    have hc : 0 ≤ C₃ * C₀' + K := by positivity
    nlinarith [mul_nonneg ha (mul_nonneg hC₃.le hc), mul_nonneg ha hK]
  calc |commQuantity d s v X (withDensityReal ρ)|
      ≤ C₁ * L * (F + lp + S + K * a) := h1
    _ ≤ C₁ * L * ((1 + C₃) * (F + (lp + (C₃ * C₀' + K) * a))) := by
        have : 0 ≤ C₁ * L := by positivity
        exact mul_le_mul_of_nonneg_left hT this
    _ = C₁ * (1 + C₃) * L * (F + (lp + (C₃ * C₀' + K) * a)) := by ring

end HRS.Commutator
