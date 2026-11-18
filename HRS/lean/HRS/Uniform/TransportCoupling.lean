import HRS.Uniform.RelativeCoupling
import HRS.Uniform.Q14Aux7

/-!
# Lemma 3.24, transport-plan coupling of the empirical and continuum noise (packet Q14)

Proof of `HRS.Uniform.transport_noise_coupling` (statement identical, relocated here because
`Comparison.lean` cannot import the Lemma 3.29 machinery): apply the adapted construction of Lemma 3.29
(`relative_covariance_coupling_proof`) to `Sg = C_N^t`, `Db = C̄_N^t`; its cost is `𝔟(C_N^t, C̄_N^t)²`, which is
bounded by `C q W₂²` by the Bures bound through an arbitrary coupling (`HRS/Uniform/Q14Aux*.lean`,
`q14_bures2_W2`).  No predictable choice of the transport plan is needed: the plan only enters the deterministic
inequality `𝔟² ≤ 2q ∑_j ∫ ‖b_{x,j} - b_{y,j}‖² dπ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

universe u

variable {d : ℕ}

open HRS.Uniform.Q14

lemma q14_isProb_withDensityReal {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

theorem transport_noise_coupling_proof (hd : 1 ≤ d) (γ : ℝ) (hγ : (d : ℝ) / 2 + 2 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (N : ℕ) (_ : 1 ≤ N) (q : ℝ) (_ : 0 ≤ q) (T : ℝ)
      (_ : 0 ≤ T) (X : ℝ → Ω → Config d N) (_ : ∀ r, Measurable[ℱ r] (X r)) (ρ : ℝ → Torus d → ℝ)
      (_ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
      (_ : ∀ x y : NegSobolev d γ, Measurable fun r => covForm γ q (withDensityReal (ρ r)) x y)
      (M : ℝ → Ω → NegSobolev d γ)
      (_ : IsHilbertMartingaleWithCovariation P ℱ T M
        (fun r ω => covForm γ q (empirical (X r ω)))),
      AdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M
        (fun r ω => covForm γ q (empirical (X r ω)))
        (fun r => covForm γ q (withDensityReal (ρ r))) (· ≤ ·)
        (fun r ω => C * q *
          (torusWassersteinE 2 (empirical (X r ω)) (withDensityReal (ρ r))).toReal ^ 2) := by
  have hS₂ := q14S_nonneg d (γ - 2)
  refine ⟨4 * d * q14S d (γ - 2) + 1, by positivity, ?_⟩
  intro Ω mΩ P _ ℱ 𝒢 N hN q hq T hT X hX ρ hρ hρm M hM
  have hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (withDensityReal (ρ r)) :=
    fun r hr => q14_isProb_withDensityReal (hρ r hr)
  have hDb : IsDetCovDensity T (fun r => covForm γ q (withDensityReal (ρ r))) := by
    refine ⟨hρm, fun σ hσ => ?_, ?_⟩
    · haveI := hdens σ hσ
      exact (q14_covForm_trace hγ hq (withDensityReal (ρ σ))).1
    · have hmeas : Measurable fun σ => traceNormForm (covForm γ q (withDensityReal (ρ σ))) :=
        measurable_traceNormForm (fun σ => covForm γ q (withDensityReal (ρ σ))) hρm
      refine Measure.integrableOn_of_bounded (M := 4 * q * d * q14S d (γ - 1))
        (by simp) hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
      haveI := hdens σ hσ
      have := (q14_covForm_trace hγ hq (withDensityReal (ρ σ))).2
      rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
      simpa using this
  obtain ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, h⟩ := relative_covariance_coupling_proof P ℱ T hT 𝒢 M _ hM
    _ hDb
  refine ⟨Ω', mΩ', P', π, ℱ', Gb, Sd, ⟨h.preserving, h.filtration, h.martingale, h.gaussian,
    h.difference, h.indep, ?_⟩⟩
  filter_upwards [h.cost] with ω' hω' r hr0 hrT
  have hrT' : r ≤ T := (ENNReal.ofReal_le_ofReal_iff hT).1 hrT
  have hr : r ∈ Set.Icc (0 : ℝ) T := ⟨hr0, hrT'⟩
  have h1 := hω' r hr0 hrT
  show traceNormForm (Sd r ω') ≤ _
  rw [h1]
  haveI := hdens r hr
  haveI := empirical_isProbabilityMeasure (Nat.pos_of_ne_zero (by omega)) (X r (π ω'))
  have h2 := q14_bures2_W2 hγ hq (empirical (X r (π ω'))) (withDensityReal (ρ r))
  refine h2.trans ?_
  have hW : 0 ≤ (torusWassersteinE 2 (empirical (X r (π ω'))) (withDensityReal (ρ r))).toReal ^ 2 :=
    sq_nonneg _
  nlinarith [mul_nonneg hq hW]

example := (@transport_noise_coupling_proof : type_of% @HRS.Uniform.transport_noise_coupling)

end Uniform

end HRS
