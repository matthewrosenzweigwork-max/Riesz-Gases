import HRS.ME.ParxUDefect1
import HRS.ME.ParxUConormal2

/-!
# Packet P3d (part 2): uniform `parxR_conormal`

Uniform version (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.parxR_conormal` (Packets:1154): an induction over `j`, with the zero step from
`hsource_conormal_aux_unif` (the uniform form of `hsource_conormal`) and the successor step from
`defect_map_unif`.  Symmetry and double centring are qualitative and use `U.H`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- The closure of the conormal classes under real multiples, as used by `hsource_conormal`. -/
theorem parxU_hSmul : ConormalSmul d :=
  fun σ b m B F hF a => ConormalL.smul hF a

/-- **Uniform version of `parxR_conormal`.** The constant for each `j` depends only on
`(d, s, N, νm, νp, c₀, Λ₀)`, on `j, m` and on the parameter facts `2 ≤ d`, `0 < s < d`,
`m ≤ N`; it is chosen before `β, V, ρ`. -/
theorem parxR_conormal_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (m : ℕ) (hN : m ≤ N) :
    ∀ j : ℕ, 2 * j ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ),
      ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal (s - (j : ℝ) / 2) 0 (m - 2 * j) (C * posSeminorm (m + 2) f)
        (parxR d s V β ρ f j) ∧
      IsSymmPair (parxR d s V β ρ f j) ∧
      HRS.PDE.DoublyCentered (withDensityReal ρ) (parxR d s V β ρ f j) := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨C, hC0, hC⟩ := hsource_conormal_aux_unif (s := s) (N := N) (νm := νm) (νp := νp)
      (c₀ := c₀) (Λ₀ := Λ₀) px4bU_hAdd parxU_hSmul hd hs0 hsd m hN
    refine ⟨C, hC0, fun β V ρ U f hf => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hC β V ρ U f hf
    refine ⟨?_, ?_, ?_⟩
    · simpa [parxR] using h1
    · intro x y
      simp only [parxR, offZero]
      by_cases hxy : x = y
      · subst hxy; rfl
      · simp only [hxy, Ne.symm hxy, ite_false]; exact h2 x y
    · simpa [parxR] using h3
  | succ j ih =>
    intro hj
    obtain ⟨C, hC0, hC⟩ := ih (by omega)
    have hσ : s - (j : ℝ) / 2 ≤ s := by
      have : (0 : ℝ) ≤ (j : ℝ) / 2 := by positivity
      linarith
    obtain ⟨CE, hCE0, hCE⟩ := defect_map_unif (s := s) (N := N) (νm := νm) (νp := νp)
      (c₀ := c₀) (Λ₀ := Λ₀) hd hs0 hsd (s - (j : ℝ) / 2) hσ 0 (m - 2 * j) (by omega) (by omega)
    refine ⟨CE * C, mul_nonneg hCE0 hC0, fun β V ρ U f hf => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hC β V ρ U f hf
    have hB0 : 0 ≤ C * posSeminorm (m + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
    have hE := hCE β V ρ U _ (parxR d s V β ρ f j) hB0 h1
    have e1 : s - (j : ℝ) / 2 - 1 / 2 = s - ((j + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
    have e2 : m - 2 * j - 2 = m - 2 * (j + 1) := by omega
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, e2] at hE
      simpa [parxR, mul_assoc] using hE
    · exact defect_symm U.H hσ (by omega) h2 h1
    · exact defect_doublyCentered U.H hσ (by omega) h2 h1 h3

end HRS.ME.ParxU

end
