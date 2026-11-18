import HRS.Prob.HilbertMartingale
import HRS.Prob.MRepAux14

/-!
# Representation of a continuous Hilbert martingale as a stochastic integral (packet MREP)

External input of Lemma 3.29 (`relative_covariance_coupling`, coupling part): every continuous square-integrable
`H`-valued martingale `M` with trace-class covariation density `Σ` is, on an enlargement of the filtered space, a
stochastic integral `∫ Φ dB` against a cylindrical Brownian motion `B` independent of the initial σ-field, with
`Φ_r Φ_r^* = Σ_r` (`hsCovForm (Φ r) = Σ r`).  Route (PROOF_QUEUE, MREP): `S = Σ^{1/2}`, `B¹ = ∫ S⁺ dM` (stochastic
integral against a general continuous Hilbert martingale), an independent Wiener enlargement for the kernel of `S`,
Lévy's characterisation.  The result is then fed to `hilbert_polar_coupling`.

Specification decisions (orchestrator 2026-10-15, ISSUES §I "MREP"):
* The conclusion represents a modification `M̃` indistinguishable from `M ∘ π` on `[0,T]`, not `M ∘ π` itself:
  `IsHilbertItoIntegral` fixes the values for `τ ≤ 0` and continuity of every path, which the martingale
  hypotheses give only almost surely on `[0,T]`.
* `Φ` vanishes after `T`, so that `IsHSIntegrand` holds for every horizon.
* Immersion: `M ∘ π` is still a Hilbert martingale with covariation `Sg ∘ π` for the enlarged filtration `ℱ'` (at all
  times, as `AdaptedGaussianCoupling` requires); true for the product enlargement with an independent Wiener factor.
* The covariation identity is per-`r` almost sure (plus its Fubini form); the pathwise form `∀ᵐ ω', ∀ r` is false in
  general (`Sg` is only entrywise measurable and adapted; independent statement review 2026-10-15, REPAIR applied).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS

universe u

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Martingale representation on an enlargement (MREP).  For a continuous `L²` Hilbert martingale `M` with
covariation density `Sg` on `[0,T]` there are an enlargement `π : Ω' → Ω` (measure preserving, filtration
extending `ℱ`), a countable cylindrical Brownian motion `B` independent of the initial σ-field `𝒢`, a
Hilbert–Schmidt integrand `Φ` (zero after `T`) with `Φ_r Φ_r^* = Sg_r ∘ π` on `[0,T]`, and `M̃ = ∫ Φ dB`
indistinguishable from `M ∘ π` on `[0,T]`. -/
theorem martingale_representation {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T) (𝒢 : InitialSigma ℱ)
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) :
    ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (ι : Type u) (_ : Countable ι) (B : ℝ≥0 → Ω' → ι → ℝ) (Φ : ℝ → Ω' → ι → H) (M' : ℝ → Ω' → H),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsCylindricalBrownian P' ℱ' B ∧
      Indep (𝒢.1.comap π) (cylindricalPathSigma B) P' ∧
      (∀ S : ℝ, IsHSIntegrand P' ℱ' S Φ) ∧
      (∀ r ω', T < r → Φ r ω' = 0) ∧
      IsHilbertMartingaleWithCovariation P' ℱ' T (fun τ ω' => M τ (π ω')) (fun r ω' => Sg r (π ω')) ∧
      IsHilbertItoIntegral P' ℱ' B Φ M' ∧
      (∀ᵐ ω' ∂P', ∀ τ ∈ Set.Icc 0 T, M' τ ω' = M τ (π ω')) ∧
      (∀ r ∈ Set.Icc 0 T, ∀ᵐ ω' ∂P', hsCovForm (Φ r ω') = Sg r (π ω')) ∧
      (∀ᵐ ω' ∂P', ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), hsCovForm (Φ r ω') = Sg r (π ω')) := by
  exact HRS.MRep.martingale_representation_aux P ℱ T hT 𝒢 M Sg hM

end HRS

end
