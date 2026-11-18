import HRS.Main.GFEVMAux8

/-!
# Packet GFEVM, part 9: `gf_ev_mat_proof`

Relocated proof of `HRS.GF.gf_ev_mat` (GFSpec1.lean).  Route: the abstract two-level construction of GFEVMAux3-5
(`GfmAbs` → `EvolData E_γ E_{γ+2}` with `IsEvolution` and the `TwoLevel` alternative), whose hypotheses are verified in
GFEVMAux1, 6-8 from the repaired `AdjointInput` (uniqueness conjunct: cocycle, linearity; existence at level `γ+2` from
the `γ` clause; the three operator bounds), the regularity `C^{γ+2d+12}` of `ρ_N`, `V` (generator in `H^γ`, continuity of
`σ ↦ 𝓛_σ` in operator norm from weak continuity of `ρ_N`) and the classical-solution calculus (Duhamel pairing).
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gf_ev_mat_proof (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (hM : Torus.SymNonpos M) (K₀ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ S : GeneralSetup d, S.Within { b with C₀ := S.C₀ } → S.MFHypM M →
      S.AdjointInput M K₀ → ∀ N : ℕ,
      ∃ EV : EvolData (NegSobolev d (S.γ : ℝ)) (NegSobolev d ((S.γ : ℝ) + 2)),
        GFEvo S M N ((S.γ : ℝ) + 2) K EV := by
  refine ⟨max K₀ 1, by linarith [le_max_right K₀ 1], fun S _ hMF hAI N => ?_⟩
  obtain ⟨EV, hEvol, hTwo, hj, hdual⟩ := gfm_abs_main (gfm_abs_setup S M K₀ hMF hAI N)
  refine ⟨EV, ⟨hEvol, Or.inl hTwo⟩, hj, hdual, ?_⟩
  intro r t hr hrt htT φ hC2 hφ
  have hγ0 : (0 : ℝ) ≤ S.γ := Nat.cast_nonneg _
  have h1 := (hAI.2 N r t hr hrt htT).1 φ hC2 (gfm_memSobolev_mono hφ (by linarith))
  have h2 := (hAI.2 N r t hr hrt htT).2 φ hC2 hφ
  exact ⟨h1.1, h2.1, h2.2.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩

example := (@gf_ev_mat_proof : type_of% @HRS.GF.gf_ev_mat)

end HRS.GF
