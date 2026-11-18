import HRS.Uniform.Q54cAux35
import HRS.Uniform.TransportCoupling

/-!
# Q54c, part 36: the noise covariance density `σ ↦ covForm n q (ρ_σ)` as a deterministic covariance density
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Torus HRS.Uniform

variable {d : ℕ}

/-- the covariance density, truncated to `[0,T]` -/
def covDens (n q T : ℝ) (μ : ℝ → Torus d → ℝ) : ℝ → NegSobolev d n →L[ℝ] NegSobolev d n →L[ℝ] ℝ :=
  fun σ => if σ ∈ Set.Icc 0 T then covForm n q (withDensityReal (μ σ)) else 0

theorem covDens_of_mem {n q T : ℝ} {μ : ℝ → Torus d → ℝ} {σ : ℝ} (h : σ ∈ Set.Icc 0 T) :
    covDens n q T μ σ = covForm n q (withDensityReal (μ σ)) := by
  unfold covDens; rw [if_pos h]

theorem covDens_continuousOn {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q) {T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hprob : ∀ σ ∈ Set.Icc 0 T, IsProbDensity (μ σ))
    (hweak : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Set.Icc 0 T))
    (hcts : ∀ σ ∈ Set.Icc 0 T, Continuous (μ σ)) (x y : NegSobolev d n) :
    ContinuousOn (fun σ => covForm n q (withDensityReal (μ σ)) x y) (Set.Icc 0 T) := by
  set fj : Fin d → Torus d → ℝ := fun j a =>
    inner ℝ (Real.sqrt (2 * q) • bVec n j a) x * inner ℝ (Real.sqrt (2 * q) • bVec n j a) y with hfj
  have hfc : ∀ j, Continuous (fj j) := fun j => by
    have hb := HRS.Uniform.Q14.q14_continuous_bVec hn j
    exact (((hb.const_smul (Real.sqrt (2 * q))).inner continuous_const)).mul
      (((hb.const_smul (Real.sqrt (2 * q))).inner continuous_const))
  have hform : ∀ σ ∈ Set.Icc 0 T, covForm n q (withDensityReal (μ σ)) x y =
      ∑ j : Fin d, ∫ a, fj j a * μ σ a := by
    intro σ hσ
    haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont (hcts σ hσ)
    rw [HRS.Uniform.Q14.q14_covForm_apply hn hq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [HRS.integral_withDensityReal_eq (μ σ) (hprob σ hσ).measurable (hprob σ hσ).nonneg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)
  refine ContinuousOn.congr ?_ (fun σ hσ => hform σ hσ)
  exact continuousOn_finset_sum _ fun j _ => hweak (fj j) (hfc j)

theorem measurable_covDens {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q) {T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hprob : ∀ σ ∈ Set.Icc 0 T, IsProbDensity (μ σ))
    (hweak : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Set.Icc 0 T))
    (hcts : ∀ σ ∈ Set.Icc 0 T, Continuous (μ σ)) (x y : NegSobolev d n) :
    Measurable fun σ => covDens n q T μ σ x y := by
  have : (fun σ => covDens n q T μ σ x y) =
      (Set.Icc (0 : ℝ) T).piecewise (fun σ => covForm n q (withDensityReal (μ σ)) x y) (fun _ => 0) := by
    funext σ
    unfold covDens
    by_cases h : σ ∈ Set.Icc 0 T
    · simp [Set.piecewise, h]
    · simp [Set.piecewise, h]
  rw [this]
  exact ContinuousOn.measurable_piecewise (covDens_continuousOn hn hq hprob hweak hcts x y)
    continuousOn_const measurableSet_Icc

theorem covDens_trace {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q) {T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hprob : ∀ σ ∈ Set.Icc 0 T, IsProbDensity (μ σ)) {σ : ℝ}
    (hσ : σ ∈ Set.Icc 0 T) :
    IsTraceClassCov (covDens n q T μ σ) ∧
      traceNormForm (covDens n q T μ σ) ≤ 4 * q * d * HRS.Uniform.Q14.q14S d (n - 1) := by
  rw [covDens_of_mem hσ]
  haveI := HRS.Uniform.q14_isProb_withDensityReal (hprob σ hσ)
  obtain ⟨h1, h2⟩ := HRS.Uniform.Q14.q14_covForm_trace hn hq (withDensityReal (μ σ))
  refine ⟨h1, ?_⟩
  simpa using h2

theorem isDetCovDensity_covDens {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q) {T : ℝ}
    {μ : ℝ → Torus d → ℝ} (hprob : ∀ σ ∈ Set.Icc 0 T, IsProbDensity (μ σ))
    (hweak : ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun r => ∫ x, ψ x * μ r x) (Set.Icc 0 T))
    (hcts : ∀ σ ∈ Set.Icc 0 T, Continuous (μ σ)) :
    IsDetCovDensity T (covDens n q T μ) := by
  have hm := fun x y => measurable_covDens hn hq hprob hweak hcts x y
  refine ⟨hm, fun σ hσ => (covDens_trace hn hq hprob hσ).1, ?_⟩
  have hmeas : Measurable fun σ => traceNormForm (covDens n q T μ σ) :=
    HRS.measurable_traceNormForm (covDens n q T μ) hm
  refine Measure.integrableOn_of_bounded (M := 4 * q * d * HRS.Uniform.Q14.q14S d (n - 1))
    (by simp) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  exact (covDens_trace hn hq hprob hσ).2

end HRS.Uniform.Q54c
