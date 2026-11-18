import HRS.Sections.Sec7Fields

/-!
# Packet L2C-6, helper 2: the susceptibility form is bounded by the variance about any constant

For a continuous probability density `ρ₁ ≤ Λ` and every constant `c`:
`C_{β,ρ₁}(ψ,ψ) ≤ K · ∫ (ψ - c)² dx`, with `K` depending on `ρ₁, Λ, β` only
(`susceptibilityCov_bounds` upper constant, then "variance is minimal at the mean" and `ρ₁ ≤ Λ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open HRS HRS.Sec7 HRS.PDE

namespace HRS.MC.L2C6Aux

variable {d : ℕ}

theorem l2c6_integrable_of_cont {μ : Measure (Torus d)} [IsFiniteMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Variance about the mean is at most the second moment about any constant, for `ρ₁ dx`, and then
`ρ₁ ≤ Λ` converts to Lebesgue measure. -/
theorem l2c6_var_le {ρ₁ : Torus d → ℝ} (h₁ : IsProbDensity ρ₁) {Λ : ℝ} (hup : ∀ x, ρ₁ x ≤ Λ)
    {ψ : Torus d → ℝ} (hψ : Continuous ψ) (c : ℝ) :
    l2Inner (withDensityReal ρ₁) (projMean (withDensityReal ρ₁) ψ) (projMean (withDensityReal ρ₁) ψ) ≤
      Λ * ∫ x, (ψ x - c) ^ 2 := by
  have : IsProbabilityMeasure (withDensityReal ρ₁) := HRS.PDE.MFSemigroup.isProb_withDensityReal h₁
  set μ₁ := withDensityReal ρ₁ with hμ₁
  have hΛ : 0 ≤ Λ := (h₁.nonneg 0).trans (hup 0)
  have hXc : Continuous fun x => ψ x - c := hψ.sub continuous_const
  have hvar := variance_le_expectation_sq (μ := μ₁) (X := fun x => ψ x - c)
    hXc.aestronglyMeasurable
  rw [variance_eq_integral hXc.aemeasurable] at hvar
  have hmean : ∫ x, (ψ x - c) ∂μ₁ = pair μ₁ ψ - c := by
    rw [integral_sub (μ := μ₁) (l2c6_integrable_of_cont hψ) (integrable_const c)]
    simp [pair]
  have e1 : l2Inner μ₁ (projMean μ₁ ψ) (projMean μ₁ ψ) = ∫ x, (ψ x - c - ∫ y, (ψ y - c) ∂μ₁) ^ 2 ∂μ₁ := by
    rw [hmean]
    unfold l2Inner projMean
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have e2 : (μ₁)[(fun x => ψ x - c) ^ 2] = ∫ x, (ψ x - c) ^ 2 ∂μ₁ := by
    rfl
  rw [e1]
  refine hvar.trans ?_
  rw [e2, HRS.PDE.MFPairing.integral_withDensityReal h₁.measurable h₁.nonneg, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
    ((l2c6_integrable_of_cont (hXc.pow 2)).const_mul Λ) (Filter.Eventually.of_forall fun x => ?_)
  · exact mul_nonneg (h₁.nonneg x) (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (hup x) (sq_nonneg _)

/-- The susceptibility form on the diagonal is bounded by `K ∫ (ψ - c)²`, uniformly in the continuous `ψ` and
the constant `c`. -/
theorem l2c6_cov_le {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ₁ : Torus d → ℝ} (h₁ : IsProbDensity ρ₁) {Λ : ℝ} (hup : ∀ x, ρ₁ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ : Torus d → ℝ, Continuous ψ → ∀ c : ℝ,
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ₁) β ψ ψ ≤ K * ∫ x, (ψ x - c) ^ 2 := by
  have : IsProbabilityMeasure (withDensityReal ρ₁) := HRS.PDE.MFSemigroup.isProb_withDensityReal h₁
  obtain ⟨c₀, C, hc₀, H⟩ := susceptibilityCov_bounds hd hs0 hsd ρ₁ h₁ Λ hup β hβ
  have hΛ : 0 ≤ Λ := (h₁.nonneg 0).trans (hup 0)
  refine ⟨max C 0 * Λ, by positivity, fun ψ hψ c => ?_⟩
  have hmem : MemLp ψ 2 (withDensityReal ρ₁) :=
    hψ.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 := (H ψ hmem).2
  have h2 := l2c6_var_le h₁ hup hψ c
  have hl0 : 0 ≤ l2Inner (withDensityReal ρ₁) (projMean (withDensityReal ρ₁) ψ)
      (projMean (withDensityReal ρ₁) ψ) :=
    integral_nonneg fun x => mul_self_nonneg _
  calc _ ≤ C * l2Inner (withDensityReal ρ₁) (projMean (withDensityReal ρ₁) ψ)
        (projMean (withDensityReal ρ₁) ψ) := h1
    _ ≤ max C 0 * l2Inner (withDensityReal ρ₁) (projMean (withDensityReal ρ₁) ψ)
        (projMean (withDensityReal ρ₁) ψ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0
    _ ≤ max C 0 * (Λ * ∫ x, (ψ x - c) ^ 2) := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    _ = _ := by ring

end HRS.MC.L2C6Aux
