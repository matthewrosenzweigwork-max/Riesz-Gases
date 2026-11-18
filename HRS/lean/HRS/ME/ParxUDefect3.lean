import HRS.ME.ParxUDefect2
import HRS.ME.ParxUNewton2

/-!
# Packet P3d (part 3): uniform `parxN_conormal`

Uniform version (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.parxN_conormal` (Packets:1194): the Newton map of `parxR_conormal_unif`, using
`newton_map_unif` at order `σ = s - j/2 < d`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `parxN_conormal`.** The constant for each `j` depends only on
`(d, s, N, νm, νp, c₀, Λ₀)`, on `j, m` and on the parameter facts `2 ≤ d`, `0 < s < d`,
`m ≤ N`; it is chosen before `β, V, ρ`. -/
theorem parxN_conormal_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (m : ℕ) (hN : m ≤ N) :
    ∀ j : ℕ, 2 * j ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ),
      ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      ConormalL (s - (j : ℝ) / 2 - 2)
        (fun c => 0 + if s - (j : ℝ) / 2 - 2 + (c : ℝ) = 0 ∧ c ≠ 1 then 1 else 0)
        (m - 2 * j) (C * posSeminorm (m + 2) f) (newtonOp d β ρ (parxR d s V β ρ f j)) := by
  intro j hj
  obtain ⟨C, hC0, hC⟩ := parxR_conormal_unif hd hs0 hsd m hN j hj
  have hσ : s - (j : ℝ) / 2 < d := by
    have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
    linarith
  obtain ⟨CN, hCN0, hCN⟩ := newton_map_unif (s := s) (N := N) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) hd hσ 0 (m - 2 * j) (by omega)
  refine ⟨CN * C, mul_nonneg hCN0 hC0, fun β V ρ U f hf => ?_⟩
  obtain ⟨h1, h2, _⟩ := hC β V ρ U f hf
  have hB0 : 0 ≤ C * posSeminorm (m + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  simpa [mul_assoc] using hCN β V ρ U _ _ hB0 h2 h1

end HRS.ME.ParxU

end
