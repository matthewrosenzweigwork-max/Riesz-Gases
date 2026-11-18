import HRS.MS.R2WfmAux6
import HRS.MS.R2QtAux1

/-!
# HRS.MS.R2WfmTie -- `round2_weighted_field_moments` (S9.7)

Packet S97, namespace `HRS.MS.R2Wfm`.

`round2_weighted_field_moments_proof : type_of% @HRS.Whole.round2_weighted_field_moments` (statement unchanged, with
`HasR2GaussianUpper` carrying `0 < c₀`; for `c₀ ≤ 0` the hypothesis is false and the assertion is vacuous).

The route is a Fourier frame (no Hermite basis, no Gaussian series): `‖T‖²_{-m,P} ≤ ∫ wt^{-m} (u² + v²) dξ` with
`u(ξ), v(ξ)` the functional applied to the weighted plane waves `⟨x⟩^P cos(2π⟨x,ξ⟩)`, `⟨x⟩^P sin(2π⟨x,ξ⟩)`; the `L^r` norms
of `u, v` are bounded by S9.5 (`round2_polynomial_moments_proof`), `‖u(ξ)‖ ≲ wt(ξ)`, and the `ξ`-integral converges since
`m ≥ d/2 + 5/2` (here `m > k + d/2 > d + 2`).  Both clauses use `s97_core_one`; the quench clause supplies
`HasR2ActualDensity` through `HRS.MS.R2Mt.s92_quench_density`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Wfm

open HRS.Whole

/-- **Corollary S9.7** (`HRS.Whole.round2_weighted_field_moments`). -/
theorem round2_weighted_field_moments_proof : type_of% @HRS.Whole.round2_weighted_field_moments := by
  intro d hd s hs0 hs M L C₀ c₀ b p K Pw hb hp hPw k m hk hm r hr
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hm' : (d : ℝ) / 2 + 5 / 2 ≤ m := by linarith
  refine ⟨?_, ?_⟩
  · by_cases hc : 0 < c₀
    · obtain ⟨C, hC⟩ := s97_core_one hd hs0 hs M L C₀ c₀ b p K Pw hc hb hp hPw m hm' r hr
      refine ⟨C, fun ρ hρ hG P hP => ?_⟩
      intro i N hN
      exact hC ρ hρ P hP hG.2 N hN
    · exact ⟨0, fun ρ _ hG => (hc hG.1).elim⟩
  · intro b₀ hb₀
    obtain ⟨p', K', hp', hK', hdens⟩ := HRS.MS.R2Mt.s92_quench_density hd hs0 hs M L b b₀ hb hb₀
    by_cases hc : 0 < c₀
    · obtain ⟨C, hC⟩ := s97_core_one hd hs0 hs M L C₀ c₀ b p' K' Pw hc hb hp' hPw m hm' r hr
      refine ⟨C, fun ρ hρ hG Kt hKt hinv => ?_⟩
      intro t N hN
      let Pt : ∀ N, Measure (EucConfig d N) := fun N =>
        (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N b₀ (HRS.Whole.withDensityReal ρ)).bind (Kt N t)
      have hP_t : ∀ N, 2 ≤ N → HasR2ActualDensity s b p' K' (HRS.Whole.withDensityReal ρ) (Pt N) :=
        fun N hN => hdens ρ hρ N hN (Kt N t) ((hKt N).markov t) (hinv N hN t)
      have key := hC ρ hρ Pt hP_t hG.2 N hN
      exact key
    · exact ⟨0, fun ρ _ hG => (hc hG.1).elim⟩

end HRS.MS.R2Wfm

example := (@HRS.MS.R2Wfm.round2_weighted_field_moments_proof : type_of% @HRS.Whole.round2_weighted_field_moments)
