import HRS.ME.ParxUPx5a1
import HRS.ME.ParxUPx5a2
import HRS.ME.ParxUPx5b1
import HRS.Equilibrium.Parametrix.PX5AuxI

/-!
# Packet P7 (assembly), part (a): the uniform gap constant

`parx_gap_unif`: the uniform form of `HRS.Parx.parx_gap_proof` (PX5AuxI). The three constants
of the proof (`Cn` from `px5_psi_bnds_unif`, `Cj` from `px5_jpair_bound_unif`, `Cr` from
`px5_remainder_unif`) are chosen before `β, V, ρ`; the constant-free fields of `ParxGapAt` are
taken from the `px5_*` lemmas with the hypothesis `U.H`.

Level hypotheses: `hs0, hsd` for the psi and jpair bounds, `hs : s = d/2` for the remainder
(`px5_remainder_unif`), and `px5m d J ≤ N`. The constant is nonnegative.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform gap lemma** (part (a)): the constant of `ParxGapAt` is chosen before `β, V, ρ`. -/
theorem parx_gap_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hs : s = (d : ℝ) / 2)
    (J : ℕ) (hN : px5m d J ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ) (U : ParxU d s N νm νp c₀ Λ₀ β V ρ),
      ParxGapAt U.H J C := by
  obtain ⟨Cn, hCn0, hCn⟩ := px5_psi_bnds_unif (N := N) (νm := νm) (νp := νp) (c₀ := c₀)
    (Λ₀ := Λ₀) hd hs0 hsd (px5m d J) hN (parxL d J) (by unfold px5m; omega)
  obtain ⟨Cj, hCj0, hCj⟩ := px5_jpair_bound_unif (N := N) (νm := νm) (νp := νp) (c₀ := c₀)
    (Λ₀ := Λ₀) hd hs0 hsd J hN
  obtain ⟨Cr, hCr0, hCr⟩ := px5_remainder_unif (N := N) (νm := νm) (νp := νp) (c₀ := c₀)
    (Λ₀ := Λ₀) hd hs J hN
  have hC : 0 ≤ Cn + Cj + Cr := by positivity
  refine ⟨Cn + Cj + Cr, hC, fun β V ρ U => ?_⟩
  have hp : ∀ f : Torus d → ℝ, 0 ≤ posSeminorm (parxK d J) f := fun f => posSeminorm_nonneg' _ _
  exact
  { C_nonneg := hC
    linear_psi := fun f f' a b hf hf' => px5_linear_psi U.H J hf hf' a b
    linear_R := fun f f' a b hf hf' => px5_linear_R U.H J hf hf' a b
    measurable := fun f hf => px5_measurable U.H J f hf
    symm := fun f hf => px5_symm U.H J f hf
    canonical := fun f hf => px5_canonical U.H J f hf
    size := fun f hf => by
      have h1 := (hCn β V ρ U f hf).mono' (K' := (Cn + Cj + Cr) * posSeminorm (parxK d J) f) (by
        rw [px5_parxK]
        exact mul_le_mul_of_nonneg_right (by linarith) (posSeminorm_nonneg' _ _))
      exact h1.psiSize (parxPsi_smooth_offDiag U.H f hf (parxL d J))
    jpair_canonical := fun f hf => px5_jpair_canonical U.H J f hf
    jpair_bound := fun f hf x y hxy => by
      refine (hCj β V ρ U f hf x y hxy).trans ?_
      rw [← px5_parxK]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith [px5_wEnv_ge_one s x y])
      exact mul_le_mul_of_nonneg_right (by linarith) (hp f)
    remainder_ck := fun f hf => by
      obtain ⟨h1, h2, h3, h4⟩ := hCr β V ρ U f hf
      exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right (by linarith) (hp f)), h4⟩
    telescope := fun f hf x y hxy => px5_telescope U.H J f hf x y hxy
    add_smooth := fun f hf Ψ hΨ x y hxy => px5_add_smooth U.H J f hf Ψ hΨ x y hxy }

end HRS.ME.ParxU

end
