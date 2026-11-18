import HRS.Equilibrium.Parametrix.PX5AuxH

/-!
# Prop 4.13 parametrix, packet PX5: the gap lemma

`parx_gap_proof`: for every `J` there is `C` with `ParxGapAt H J C` (statement of `parx_gap`;
proved here, downstream of `Packets.lean`, because the helper files import `Packets.lean`).
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem Px5Bnds.mono' {K K' : ℝ} {ψ : Torus d → Torus d → ℝ} (h : Px5Bnds s K ψ) (hK : K ≤ K') :
    Px5Bnds s K' ψ := by
  refine ⟨h.smooth2, fun x y hxy => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · exact (h.size x y hxy).trans (mul_le_mul_of_nonneg_right hK
      (by linarith [px5T_ge_one s 0 (px5_rTrunc_nonneg x y)]))
  · exact (h.grad p hp).trans (mul_le_mul_of_nonneg_right hK
      (by linarith [px5T_ge_one s 1 (px5_rTrunc_nonneg (Torus.mk p.1) (Torus.mk p.2))]))
  · exact (h.hess p hp).trans (mul_le_mul_of_nonneg_right hK
      (by linarith [px5T_ge_one s 2 (px5_rTrunc_nonneg (Torus.mk p.1) (Torus.mk p.2))]))

/-- **The gap lemma** (statement of `parx_gap`). -/
theorem parx_gap_proof (H : ParxHyp d s V β ρ) (J : ℕ) : ∃ C : ℝ, ParxGapAt H J C := by
  obtain ⟨Cn, hCn0, hCn⟩ := px5_psi_bnds H (px5m d J) (parxL d J) (by unfold px5m; omega)
  obtain ⟨Cj, hCj0, hCj⟩ := px5_jpair_bound H J
  obtain ⟨Cr, hCr0, hCr⟩ := px5_remainder H J
  refine ⟨Cn + Cj + Cr, ?_⟩
  have hp : ∀ f : Torus d → ℝ, 0 ≤ posSeminorm (parxK d J) f := fun f => posSeminorm_nonneg' _ _
  exact
  { C_nonneg := by positivity
    linear_psi := fun f f' a b hf hf' => px5_linear_psi H J hf hf' a b
    linear_R := fun f f' a b hf hf' => px5_linear_R H J hf hf' a b
    measurable := fun f hf => px5_measurable H J f hf
    symm := fun f hf => px5_symm H J f hf
    canonical := fun f hf => px5_canonical H J f hf
    size := fun f hf => by
      have h1 := (hCn f hf).mono' (K' := (Cn + Cj + Cr) * posSeminorm (parxK d J) f) (by
        rw [px5_parxK]
        exact mul_le_mul_of_nonneg_right (by linarith) (posSeminorm_nonneg' _ _))
      exact h1.psiSize (parxPsi_smooth_offDiag H f hf (parxL d J))
    jpair_canonical := fun f hf => px5_jpair_canonical H J f hf
    jpair_bound := fun f hf x y hxy => by
      refine (hCj f hf x y hxy).trans ?_
      rw [← px5_parxK]
      refine mul_le_mul_of_nonneg_right ?_ (by linarith [px5_wEnv_ge_one s x y])
      exact mul_le_mul_of_nonneg_right (by linarith) (hp f)
    remainder_ck := fun f hf => by
      obtain ⟨h1, h2, h3, h4⟩ := hCr f hf
      exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right (by linarith) (hp f)), h4⟩
    telescope := fun f hf x y hxy => px5_telescope H J f hf x y hxy
    add_smooth := fun f hf Ψ hΨ x y hxy => px5_add_smooth H J f hf Ψ hΨ x y hxy }

example := (@parx_gap_proof : type_of% @parx_gap)

end HRS.Parx

end
