import HRS.MS.R2PolyAux2

/-!
# HRS.MS.R2PolyTie -- `round2_polynomial_moments` (S9.5)

Packet S95, namespace `HRS.MS.R2Poly`.

`round2_polynomial_moments_proof : type_of% @HRS.Whole.round2_polynomial_moments` (statement unchanged, with
`HasR2GaussianUpper` carrying `0 < c₀`; for `c₀ ≤ 0` the hypothesis is false and the assertion is vacuous).

Proof (TeX S L7137-7163): cut `h = ∑_k h_k` along the annuli `k - 1 < max(|x|,|y|) ≤ k` (sharp cutoffs suffice).  Each
piece lies in the bounded class `IsBoundedPairKernel s (B 2^P (1+k)^P)`, so the quantitative form `s95_F_small` of the S9.2
moment transfer (the `L²(μ⊗μ)` mass of the piece, `s95_ann_L2`, decays like `e^{-c₀k/2}` by the Gaussian tail) gives a
summable family of `L^r(P_N)` bounds; `pairEnergy` is linear in the kernel and converges along the partial sums
(`s95_pe_tendsto`, using the weighted moment bounds of `s95_poly_int`), and Fatou (`s95_lim_bound`) passes to the limit.
The tail is dominated convergence over `k` (`s95_conj2`); the linear bound is the same scheme for test functions with the
Hoeffding bound interpolated against the `L²` mass (`s95_lin_small`, `s95_conj3`).  The auxiliary files are `R2PolyAux1/2`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Poly

open HRS.Whole HRS.MS.R2Mt

/-- **Proposition S9.5** (`HRS.Whole.round2_polynomial_moments`). -/
theorem round2_polynomial_moments_proof : type_of% @HRS.Whole.round2_polynomial_moments := by
  intro d hd s hs0 hs M L C₀ c₀ b p K Pw hb hp hPw r hr
  by_cases hc : 0 < c₀
  · obtain ⟨C1, hC1, h1⟩ := s95_conj1 hd hs0 hs M L C₀ c₀ b p K r Pw hc hb hp hr hPw
    obtain ⟨C3, hC3, h3⟩ := s95_conj3 hd hs0 hs M L C₀ c₀ b p K r Pw hc hb hp hr hPw
    refine ⟨max C1 C3, fun ρ hρ hG P hP => ⟨?_, ?_, ?_⟩⟩
    · intro B hB h hh i N hN
      obtain ⟨u, v⟩ := h1 ρ hρ hG.2 N hN (P N) (hP N hN) B hB h hh
      exact ⟨u.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hB)),
        v.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hB))⟩
    · intro B hB h hj hh hhj ⟨ε, hε, hεs, hconv⟩
      haveI := s92_isProb_mu hρ.prob
      have hle : ∀ j, eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2) (ENNReal.ofReal 2)
          ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ≤
          eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2) (ENNReal.ofReal (2 + ε))
          ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := fun j =>
        eLpNorm_le_eLpNorm_of_exponent_le (p := ENNReal.ofReal 2) (q := ENNReal.ofReal (2 + ε))
          (ENNReal.ofReal_le_ofReal (by linarith))
      have hconv2 : Tendsto (fun j => eLpNorm (fun q : Euc d × Euc d => hj j q.1 q.2 - h q.1 q.2)
          (ENNReal.ofReal 2) ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv (fun j => zero_le') hle
      exact s95_conj2 hd hs0 hs M L C₀ c₀ b p K r Pw hc hb hp hr hPw ρ hρ hG.2 P hP B hB h hj hh hhj hconv2
    · intro B hB N hN a ha hab
      exact (h3 ρ hρ hG.2 N hN (P N) (hP N hN) B hB a ha hab).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hB))
  · exact ⟨0, fun ρ _ hG => (hc hG.1).elim⟩

end HRS.MS.R2Poly

example := (@HRS.MS.R2Poly.round2_polynomial_moments_proof : type_of% @HRS.Whole.round2_polynomial_moments)
