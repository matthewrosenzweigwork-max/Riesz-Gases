/-
# HRS.Equilibrium.Preparation — preparation endpoints (EQ-01d)

Section 4.O of the main manuscript (source lines 5571-5656): Proposition 4.25
`M:O:prop:log-prep` (logarithmic preparation endpoint, external input Delgadino-Gvalani-
Rosenzweig, *Sharp...*, Theorems 2.2 and 2.6), Proposition 4.26 `M:O:prop:entropy-endpoint`
(zero-preparation entropy endpoint), and the divergence statement of the paragraph "Why the
positive-power argument differs" (source lines 5651-5656; coverage row `M:@remark:L891`).

Partition functions at possibly negative parameters are written as `lintegral`s
(`modNormalizerE`), because the Bochner normaliser `gibbsNormalizer` is `0` when the integrand
is not integrable, which would make an upper bound vacuous.
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.PreparationAux
import HRS.Equilibrium.PreparationAttractive
import HRS.Equilibrium.RepulsiveSpec

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-- `K_{N,γ}(μ) = ∫ e^{-γ N F_N(X_N, μ)} dμ^{⊗N}` in `ℝ≥0∞` (`H:eq:modulated-gibbs`, line 450),
valid for every real `γ`. -/
def modNormalizerE (g : Torus d → ℝ) (N : ℕ) (γ : ℝ) (μ : Measure (Torus d)) : ℝ≥0∞ :=
  ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-γ * N * modulatedEnergyKernel g X μ))
    ∂(Measure.pi fun _ => μ)

/-- The repulsive half of Proposition 4.25 (`O:eq:small-negative`, `0 ≤ γ ≤ B₀`): the uniform
partition-function bound for the periodic logarithm with nonnegative inverse temperature, the
torus version of Delgadino-Gvalani-Rosenzweig Theorem 2.2 (cited at source line 5609).
The repository `dgrhs-lean` proves Theorem 2.2 only on `ℝ^d`
(`DGRHS.CLT.sourceLogSingularPartition_uniform`); its periodic variant is incomplete there
(`research/statement-map.md`, row 2.1). The torus proof is the package REP-01..REP-07
(`HRS/Equilibrium/Repulsive*.lean`, plan in `docs/REPULSIVE_PLAN.md`); `log_prep_repulsive`
follows from its final step. -/
theorem log_prep_repulsive (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (B₀ : ℝ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (0 : ℝ) B₀,
      modNormalizerE (periodicRiesz d 0) N γ (withDensityReal ρ) ≤ ENNReal.ofReal C := by
  exact Repulsive.log_prep_repulsive_aux hd ρ hρ Λ hΛ B₀

/-- Proposition 4.25 `M:O:prop:log-prep` (source lines 5588-5593), `O:eq:small-negative`: for
the periodic logarithm and `μ` with a bounded density there is `a_* > 0` such that for every
finite `B₀`, `sup_{N ≥ 2} sup_{-a_* ≤ γ ≤ B₀} K_{N,γ}(μ) < ∞`. (External: DGR Theorem 2.6 and
Remark 2.1 for the attractive side, Theorem 2.2 for the repulsive side.) -/
theorem log_prep_small_negative (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ a : ℝ, 0 < a ∧ ∀ B₀ : ℝ, ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) B₀,
      modNormalizerE (periodicRiesz d 0) N γ (withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨a, ha, C₁, hC₁⟩ := log_prep_attractive hd ρ hρ Λ hΛ
  refine ⟨a, ha, fun B₀ => ?_⟩
  obtain ⟨C₂, hC₂⟩ := log_prep_repulsive hd ρ hρ Λ hΛ B₀
  refine ⟨max C₁ C₂, fun N hN γ hγ => ?_⟩
  rcases le_total γ 0 with h | h
  · exact (hC₁ N hN γ ⟨hγ.1, h⟩).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · exact (hC₂ N hN γ ⟨h, hγ.2⟩).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

/-- Proposition 4.25, `O:eq:prep-uniform` (source lines 5594-5600): for each finite `B, B₀`
there is `p > 1` with
`sup_{N≥2} sup_{0≤β≤B} sup_{0≤β₀≤B₀} ∫ (dQ_{N,β₀}(μ)/dQ_{N,β}(μ))^p dQ_{N,β}(μ) < ∞`. -/
theorem log_prep_uniform (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (B B₀ : ℝ) :
    ∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc (0 : ℝ) B,
      ∀ β₀ ∈ Set.Icc (0 : ℝ) B₀,
        modulatedGibbs (periodicRiesz d 0) N β₀ (withDensityReal ρ) ≪
            modulatedGibbs (periodicRiesz d 0) N β (withDensityReal ρ) ∧
          ∫⁻ X, ((modulatedGibbs (periodicRiesz d 0) N β₀ (withDensityReal ρ)).rnDeriv
              (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal ρ)) X) ^ p
              ∂(modulatedGibbs (periodicRiesz d 0) N β (withDensityReal ρ)) ≤
            ENNReal.ofReal C := by
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hg : Measurable (periodicRiesz d 0) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have hgi : Integrable (periodicRiesz d 0) := KernelAux.integrable_periodicRiesz hd hs0 hsd
  haveI := isProb_withDensityReal hρ
  have hI := PreparationAux.integrable_pair_withDensity hg hgi ρ Λ hΛ (ν := withDensityReal ρ) rfl
  exact PreparationAux.uniform_of_small_negative hg hI (log_prep_small_negative hd ρ hρ Λ hΛ) B B₀

/-- Proposition 4.26 `M:O:prop:entropy-endpoint` (source lines 5634-5639),
`O:eq:entropy-endpoint`: fix `B ≥ 0` and a reference probability measure `μ` with
`∬ |g| dμ^{⊗2} < ∞` (so `|I| < ∞`), and suppose `log K_{N,γ}(μ) ≤ C N δ_N` for
`γ ∈ [0, B + 1]` and `N ≥ 2`. Then `H(Q_{N,β₀}(μ) | Q_{N,β}(μ)) ≤ C' N δ_N` uniformly for
`β, β₀ ∈ [0, B]`, including `β₀ = 0`. (`N δ_N ≥ 1` holds for the `δ_N` of `deltaN`.) -/
theorem entropy_endpoint {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (B : ℝ) (hB : 0 ≤ B)
    (hI : Integrable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2)) (μ.prod μ))
    (Cp : ℝ) (hpress : ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (0 : ℝ) (B + 1),
      modNormalizerE (periodicRiesz d s) N γ μ ≤ ENNReal.ofReal (Real.exp (Cp * N * deltaN d s N))) :
    ∃ C' : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ β₀ ∈ Set.Icc (0 : ℝ) B,
      relEntropy (modulatedGibbs (periodicRiesz d s) N β₀ μ)
          (modulatedGibbs (periodicRiesz d s) N β μ) ≤
        ENNReal.ofReal (C' * N * deltaN d s N) := by
  have hg : Measurable (periodicRiesz d s) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  set A := |∫ p : Torus d × Torus d, periodicRiesz d s (p.1 - p.2) ∂(μ.prod μ)| with hA
  refine ⟨(B * (A / 2 + B * (A / 2) + |Cp|) + |Cp| + B * (A / 2)), fun N hN β hβ β₀ hβ₀ => ?_⟩
  have hL := PreparationAux.one_le_N_deltaN (d := d) hs0 N (by omega)
  have hpress' : ∀ γ ∈ Set.Icc (0 : ℝ) (B + 1),
      PreparationAux.KE (periodicRiesz d s) N γ μ ≤
        ENNReal.ofReal (Real.exp (Cp * ((N : ℝ) * deltaN d s N))) := by
    intro γ hγ
    have := hpress N hN γ hγ
    rwa [← mul_assoc]
  have := PreparationAux.entropy_bound_aux hg hI (N := N) (by omega) B Cp ((N : ℝ) * deltaN d s N)
    hB hL hpress' β hβ β₀ hβ₀
  rwa [mul_assoc]

/-- The exact entropy identity in the proof of Proposition 4.26 (source lines 5644-5647):
`H(Q_{N,β₀} | Q_{N,β}) = (β - β₀) E_{Q_{N,β₀}}[N F_N] + f(β) - f(β₀)`, `f = log K_{N,·}`,
for `0 ≤ β, β₀`, given `∬|g| dμ^{⊗2} < ∞` and finite partition functions at `β` and at
`β₀ + 1` (the latter gives the exponential moment of the negative part of `N F_N` used in the
source to differentiate at `β₀`). -/
theorem relEntropy_modulatedGibbs_eq {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (hI : Integrable (fun p : Torus d × Torus d => periodicRiesz d s (p.1 - p.2)) (μ.prod μ))
    (N : ℕ) (hN : 2 ≤ N) (β β₀ : ℝ) (hβ : 0 ≤ β) (hβ₀ : 0 ≤ β₀)
    (hfin : modNormalizerE (periodicRiesz d s) N β μ < ∞)
    (hfin₀ : modNormalizerE (periodicRiesz d s) N (β₀ + 1) μ < ∞) :
    Integrable (fun X : Config d N => (N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X μ)
        (modulatedGibbs (periodicRiesz d s) N β₀ μ) ∧
      relEntropy (modulatedGibbs (periodicRiesz d s) N β₀ μ)
          (modulatedGibbs (periodicRiesz d s) N β μ) =
        ENNReal.ofReal ((β - β₀) * ∫ X, (N : ℝ) * modulatedEnergyKernel (periodicRiesz d s) X μ
            ∂(modulatedGibbs (periodicRiesz d s) N β₀ μ) +
          Real.log (modNormalizerE (periodicRiesz d s) N β μ).toReal -
          Real.log (modNormalizerE (periodicRiesz d s) N β₀ μ).toReal) := by
  have hg : Measurable (periodicRiesz d s) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  exact PreparationAux.relEntropy_eq_aux hg hI β β₀ hβ₀ hfin.ne hfin₀.ne

/-- Source lines 5651-5656 (`O:eq:power-divergence`): for `0 < s < d` and a bounded reference
density bounded below on an open ball, `K_{N,-a}(μ) = ∞` for every `a > 0` and `N ≥ 2`; so the
ratio identity `O:eq:ratio` at `β₀ = 0` gives no `L^{1+ε}` moment for positive Riesz exponents. -/
theorem modNormalizer_neg_eq_top {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (x₀ : Torus d)
    (r c : ℝ) (hr : 0 < r) (hc : 0 < c) (hball : ∀ x, Torus.eucDist x x₀ < r → c ≤ ρ x)
    (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 2 ≤ N) :
    modNormalizerE (periodicRiesz d s) N (-a) (withDensityReal ρ) = ∞ :=
  PreparationAux.KE_neg_eq_top hd hs0 hsd ρ hρ Λ hΛ x₀ r c hr hc hball a ha N hN

end HRS

end
