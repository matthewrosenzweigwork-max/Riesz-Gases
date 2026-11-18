import HRS.ME.ParxUDefect2
import HRS.Equilibrium.Parametrix.PX5AuxC

/-!
# Packet P4b (part 1): uniform `px5_remainder`

Uniform version (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.px5_remainder` (PX5AuxC:166), which is the `remainder_ck` field of `ParxGapAt`.
The constant is built from `parxR_conormal_unif` (the uniform form of `parxR_conormal`) and
`conormal_extend` (which does not involve `ρ`).  The qualitative facts (double centring of the
diagonal extension, symmetry) come from `px5_dc_diagExt` and from `U.H`-independent arguments.

The hypothesis `hs : s = d / 2` is the `crit` field of `ParxHyp`, now a parameter (it fixes the
numerology `σ_L + J + 1 = -2 < 0` of `conormal_extend` without reference to `β, V, ρ`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `px5_remainder`.** For fixed `J`, the constant depends only on
`(d, s, N, νm, νp, c₀, Λ₀, J)`; it is chosen before `β, V, ρ`.  The level `N` must dominate
`px5m d J = (J+1) + 2 L` with `L = parxL d J`. -/
theorem px5_remainder_unif (hd : 2 ≤ d) (hs : s = (d : ℝ) / 2) (J : ℕ) (hN : px5m d J ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      HRS.PDE.IsCk2 J (diagExt (parxR d s V β ρ f (parxL d J))) ∧
      HRS.PDE.DoublyCentered (withDensityReal ρ) (diagExt (parxR d s V β ρ f (parxL d J))) ∧
      HRS.PDE.cbNorm2 J (diagExt (parxR d s V β ρ f (parxL d J))) ≤ C * posSeminorm (parxK d J) f ∧
      (∀ x y, diagExt (parxR d s V β ρ f (parxL d J)) x y =
        diagExt (parxR d s V β ρ f (parxL d J)) y x) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd : s < d := by rw [hs]; linarith
  have hL : 2 * parxL d J ≤ px5m d J := by unfold px5m; omega
  obtain ⟨C, hC0, hC⟩ := parxR_conormal_unif hd hs0 hsd (px5m d J) hN (parxL d J) hL
  have e : px5m d J - 2 * parxL d J = J + 1 := by unfold px5m; omega
  have hσ : s - (parxL d J : ℝ) / 2 + ((J : ℝ) + 1) < 0 := by
    have hc : (parxL d J : ℝ) = 2 * J + d + 6 := by unfold parxL; push_cast; ring
    rw [hc, hs]; linarith
  obtain ⟨Ce, hCe0, hCe⟩ := conormal_extend hd J (s - (parxL d J : ℝ) / 2) 0 hσ
  refine ⟨Ce * C, mul_nonneg hCe0 hC0, fun β V ρ U f hf => ?_⟩
  obtain ⟨hcl, hsym, hdc⟩ := hC β V ρ U f hf
  rw [e] at hcl
  have hB0 : 0 ≤ C * posSeminorm (px5m d J + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  obtain ⟨h1, h2, h3⟩ := hCe _ _ hB0 hcl
  refine ⟨h1, px5_dc_diagExt (by omega) hdc, ?_, ?_⟩
  · rw [px5_parxK]
    calc _ ≤ Ce * (C * posSeminorm (px5m d J + 2) f) := h2
      _ = _ := by ring
  · intro x y
    by_cases hxy : x = y
    · subst hxy; rfl
    · have hyx : y ≠ x := Ne.symm hxy
      rw [h3 x y hxy, h3 y x hyx]
      exact hsym x y

end HRS.ME.ParxU

end
