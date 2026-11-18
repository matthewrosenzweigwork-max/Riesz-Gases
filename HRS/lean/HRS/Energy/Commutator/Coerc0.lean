import HRS.Energy.Commutator.Basic

/-!
# Nonnegativity of `F_N + o_N` (packet CM-NN)

The inequality `|Comm_N| ≤ C K (F_N + o_N)` can only be deduced from `|Comm_N| ≤ C (L+F) (F_N + o_N)`
and `L + F ≤ K` if `F_N + o_N ≥ 0` (coercivity, lower bound of the modulated energy).  This is
`HRS.CoercAux.coercivity_energy` (`Esq ≥ 0` and `Esq ≤ 2(F_N + o_N)`), already proved in
`Coercivity.lean` (heat truncation, `rieszEnergy_ge_aux`).  After the file split of the plan (§8)
the helper sections `CoercAux` live in `HRS/Energy/CoercivityAux.lean`, imported here instead of
`Coercivity.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- `F_N + o_N ≥ 0` with a suitable `C₀`; if it holds for `C₀` it holds for every larger one
(`oNΛ_mono`). -/
theorem energy_add_oN_nonneg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N := by
  obtain ⟨C₀, hC₀, h⟩ := HRS.CoercAux.coercivity_energy hd hs0 hsd
  refine ⟨C₀, hC₀, fun Λ hΛ N hN ρ hρ hρΛ X hX => ?_⟩
  obtain ⟨h1, h2⟩ := h Λ hΛ N hN ρ hρ hρΛ X hX
  linarith

end HRS.Commutator
