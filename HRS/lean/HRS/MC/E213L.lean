import HRS.Main.Headline

/-!
# Packet e213l: the susceptibility covariance at `β₀ = 0` is the i.i.d. bridge covariance

`responseInverse g μ 0 ψ` is a `choose`; at `β = 0` the response equation `h + 0 • K h = P_μ ψ`
forces `h =ᵐ[μ] P_μ ψ`, so `C_{0,μ}(φ,ψ) = ⟨P_μ φ, P_μ ψ⟩_{L²(μ)} = μ(φψ) - μ(φ) μ(ψ)`.

Hypotheses actually used: `μ` a probability measure and `φ, ψ` continuous (smooth tests are
continuous). The kernel `g` is arbitrary. Consequently `Main.preparedCov d s β₀ μ = susceptibilityCov
(periodicRiesz d s) μ β₀` on smooth tests for every `β₀` (the case `β₀ ≠ 0` is by definition).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MC.E213L

variable {d : ℕ}

lemma e213l_memLp {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : MemLp f 2 μ :=
  hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

lemma e213l_integrable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- At `β = 0` the response `R_{0,μ} P_μ ψ` is `P_μ ψ` `μ`-a.e. -/
lemma e213l_responseInverse_zero_ae {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (g : Torus d → ℝ) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    responseInverse g μ 0 ψ =ᵐ[μ] projMean μ ψ := by
  have hex : ∃ h, IsResponse g μ 0 ψ h := by
    refine ⟨projMean μ ψ, ?_, ?_, ?_⟩
    · exact (e213l_memLp hψ).sub (memLp_const _)
    · have hi := e213l_integrable (μ := μ) hψ
      simp only [pair, projMean]
      rw [integral_sub hi (integrable_const _)]
      simp [pair]
    · exact Filter.Eventually.of_forall fun x => by simp
  have hspec := hex.choose_spec
  have h : responseInverse g μ 0 ψ = hex.choose := by
    unfold responseInverse; exact dif_pos hex
  rw [h]
  filter_upwards [hspec.2.2] with x hx
  simpa using hx

/-- `C_{0,μ}(φ,ψ) = Cov_μ(φ,ψ)`: the susceptibility covariance at `β = 0` is `iidCov`. -/
theorem e213l_susceptibilityCov_zero {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (g : Torus d → ℝ) {φ ψ : Torus d → ℝ} (hφ : Continuous φ) (hψ : Continuous ψ) :
    susceptibilityCov g μ 0 φ ψ = iidCov μ φ ψ := by
  unfold susceptibilityCov l2Inner
  have h1 : ∫ x, projMean μ φ x * responseInverse g μ 0 ψ x ∂μ
      = ∫ x, projMean μ φ x * projMean μ ψ x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [e213l_responseInverse_zero_ae (μ := μ) g hψ] with x hx
    rw [hx]
  rw [h1]
  have hφi := e213l_integrable (μ := μ) hφ
  have hψi := e213l_integrable (μ := μ) hψ
  have hφψ := e213l_integrable (μ := μ) (hφ.mul hψ)
  have e : ∀ x, projMean μ φ x * projMean μ ψ x
      = φ x * ψ x - pair μ ψ * φ x - pair μ φ * ψ x + pair μ φ * pair μ ψ := by
    intro x; simp only [projMean]; ring
  simp_rw [e]
  have i1 : Integrable (fun x => φ x * ψ x) μ := hφψ
  have i2 : Integrable (fun x => pair μ ψ * φ x) μ := hφi.const_mul _
  have i3 : Integrable (fun x => pair μ φ * ψ x) μ := hψi.const_mul _
  have i4 : Integrable (fun x => φ x * ψ x - pair μ ψ * φ x) μ := i1.sub i2
  have i5 : Integrable (fun x => φ x * ψ x - pair μ ψ * φ x - pair μ φ * ψ x) μ := i4.sub i3
  rw [integral_add i5 (integrable_const _), integral_sub i4 i3,
    integral_sub i1 i2, integral_const_mul, integral_const_mul]
  simp only [iidCov, pair, integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Smooth tests, `μ = ρ dx` with `ρ` a smooth positive probability density, the periodic Riesz
kernel: `susceptibilityCov (periodicRiesz d s) μ 0 φ ψ = iidCov μ φ ψ`. -/
theorem e213l_susceptibilityCov_zero_smooth {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (s : ℝ)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) 0 φ ψ
      = iidCov (withDensityReal ρ) φ ψ := by
  haveI := PoleCavityAux.isProbabilityMeasure_mu hρ
  exact e213l_susceptibilityCov_zero _ (StaticLimitAux.continuous_of_smooth hφ)
    (StaticLimitAux.continuous_of_smooth hψ)

/-- `preparedCov` coincides with `susceptibilityCov` at `β₀`, for every `β₀` (in particular
`β₀ ≥ 0`), on smooth tests and probability `μ`. -/
theorem e213l_preparedCov_eq_susceptibilityCov {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (s β₀ : ℝ) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    Main.preparedCov d s β₀ μ φ ψ = susceptibilityCov (periodicRiesz d s) μ β₀ φ ψ := by
  unfold Main.preparedCov
  split_ifs with h
  · subst h
    exact (e213l_susceptibilityCov_zero _ (StaticLimitAux.continuous_of_smooth hφ)
      (StaticLimitAux.continuous_of_smooth hψ)).symm
  · rfl

/-- The same for `μ = ρ dx`, `SmoothPosDensity ρ` (the form used by `IsGaussianLimitField`). -/
theorem e213l_preparedCov_eq_susceptibilityCov_density {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (s β₀ : ℝ) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    Main.preparedCov d s β₀ (withDensityReal ρ) φ ψ
      = susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β₀ φ ψ := by
  haveI := PoleCavityAux.isProbabilityMeasure_mu hρ
  exact e213l_preparedCov_eq_susceptibilityCov s β₀ hφ hψ

end HRS.MC.E213L
