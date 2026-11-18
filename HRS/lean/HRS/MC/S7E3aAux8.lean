import HRS.MC.S7E3aAux7
import HRS.MC.S7E3aAux4

/-!
# Packets `s7_E3a/b`, file 8: the two-sided bounds for the cut-off chaos

For `0 <= s < d` and the chaos limits `Q_eps` of `hCut d s phi eps`:
`E Q_eps^2 <= (1/2) ||h°_eps||^2` and, for every `eta > 0`, a constant `K` with
`(1 - 4 eta)/2 ||h°_eps||^2 - K <= E Q_eps^2` for all small `eps`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E3Aux8

open HRS HRS.Sec7

variable {d : ℕ}

theorem e3_two_sided (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ)
    (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hG : s7_GaussData d s β ρ e P G) (Q : ℝ → Ω → ℝ)
    (hQ : ∀ ε, 0 < ε → AEMeasurable (Q ε) P ∧ s7_IsChaosLimit d s β ρ e P G (hCut d s φ ε) (Q ε)) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ ω, Q ε ω ^ 2 ∂P ≤ s7_hcNorm2 d ρ (hCut d s φ ε) / 2) ∧
    ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (1 - 4 * η) / 2 * s7_hcNorm2 d ρ (hCut d s φ ε) - K ≤ ∫ ω, Q ε ω ^ 2 ∂P := by
  obtain ⟨c, hc0, hc1, hall⟩ := E1.s7_E1_variance_sandwich_proof hd hs0 hsd hβ ρ hρ
  have hadm := (E1b.s7_E1b_cutoff_kernel_admissible_proof hd hs0 hsd ρ hρ φ hφ).1
  refine ⟨?_, fun η hη => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    obtain ⟨hm, hsy, hL2⟩ := hadm ε hε
    have := (hall e he P G hG _ hm hsy hL2 (Q ε) (hQ ε hε).1 (hQ ε hε).2).2.2.2
    linarith
  · obtain ⟨S, hS0, hS⟩ := E3Aux4.e3_row_bound hd hs0 hsd hρ hφ he
    obtain ⟨N, hN⟩ := E3Aux6.e3_lower_bound hd hs0 hsd hβ hρ he hη
    refine ⟨2 * N * S ^ 2, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    obtain ⟨hm, hsy, hL2⟩ := hadm ε hε
    exact hN P G hG _ hm hsy hL2 (hS ε hε) (Q ε) (hQ ε hε).1 (hQ ε hε).2

end HRS.MC.Sec7.E3Aux8

end
