import HRS.Energy.Commutator.BesselKernel

/-!
# Route H, packet H3: energy control by the truncated kernel (`[HCRS] Prop. 2.11`, Cor. 2.13)

`F_N = (1/2N²)∑_{i≠j} f_η(x_i-x_j) + ½ E_η - g_η(0)/(2N) - N⁻¹∑_i (f_η*μ)(x_i) + ½ ∬ f_η dμ dμ`,
where `E_η = ∬ g_η d(μ_N-μ)^{⊗2} = ∑_k ĝ_η(k) |μ̂_N(k) - μ̂(k)|² ≥ 0` (diagonal reinserted:
`g_η` is bounded, the diagonal contributes `g_η(0)/N`).  With `H2.4` the last two terms are
`O(Λ η^{d-s})`.  The existing `CoercAux.Esq/Q_eq_tsum/integral_trigSum_sub` do the same Fourier
bookkeeping for the heat truncation; reuse them verbatim (they only use `cT ≥ 0` and summability).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- The truncated energy `E_η = ∑_k ĝ_η(k) |μ̂_N(k) - μ̂(k)|²`. -/
def etaEnergy (d : ℕ) (s η : ℝ) {N : ℕ} (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  ∑' k : Lattice d, truncCoeff d s η k *
    ‖((N : ℝ)⁻¹ : ℝ) • ∑ i, Torus.mode k (X i) - ∫ x, Torus.mode k x ∂μ‖ ^ 2

theorem etaEnergy_nonneg (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {η : ℝ} (hη : 0 < η) {N : ℕ}
    (X : Config d N) (μ : Measure (Torus d)) : 0 ≤ etaEnergy d s η X μ := by
  sorry

/-- **H3.1 (`[HCRS] (2.46)`, torus).**  `C = C(d,s)`; the three terms on the left are
(up to the `O(η^{d-s})` lower bound `fEta_ge`) nonnegative. -/
theorem energy_control_bessel (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ (N : ℕ), 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, fEta d s η (X i - X j)
            + (1 / 2) * etaEnergy d s η X (withDensityReal ρ) ≤
          rieszEnergy d s X (withDensityReal ρ) + gEta d s η 0 / (2 * N) + C * Λ * η ^ ((d : ℝ) - s) := by
  sorry

/-- Evaluation of the self energy `g_η(0)/(2N)` and of `Λ η^{d-s}` at `η = c λ`, `λ = (NΛ)^{-1/d}`:
both are `≲ a_N^Λ` (`s > 0`), resp. `logPart + O(a_N^Λ)` with coefficient one on the logarithm
(`s = 0`, `H2.1`; uses `CoercAux.smear_neg_eq`, `smear_a_eq`, `smear_log_eq`). -/
theorem gEta_zero_le_oN (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      gEta d s (c * smearScale d N Λ) 0 / (2 * N) ≤ logPart d s Λ N + C * aNΛ d s Λ N ∧
      Λ * (c * smearScale d N Λ) ^ ((d : ℝ) - s) ≤ aNΛ d s Λ N := by
  sorry

end HRS.Commutator
