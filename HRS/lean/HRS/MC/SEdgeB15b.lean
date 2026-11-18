import HRS.MC.SEdgeVocab

/-!
# Packet B15b: smooth solutions of the response equation are the `responseInverse` class
(relocation of `sed_B15b_ae_unique`)

Proof of the statement `HRS.MC.SEdge.sed_B15b_ae_unique` (SEdgeSpec.lean) in its own file.  The spec theorem
stays `sorry`; the `example` at the end ties this proof to it by `type_of%`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B15b

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem b15b_continuous {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  HRS.Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf).continuous

theorem b15b_bound {f : Torus d → ℝ} (hf : Continuous f) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

theorem b15b_integrable {f : Torus d → ℝ} (hf : Continuous f) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] : Integrable f μ := by
  obtain ⟨C, hC⟩ := b15b_bound hf
  exact (MemLp.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x)).integrable one_le_two

theorem b15b_memLp {f : Torus d → ℝ} (hf : Continuous f) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] : MemLp f 2 μ := by
  obtain ⟨C, hC⟩ := b15b_bound hf
  exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC x)

/-- For a probability measure, the centred function `h - mu(h)` has mean zero (also when `h` is not
integrable, since then `mu(h) = 0` by convention). -/
theorem b15b_projMean_integral_zero (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (h : Torus d → ℝ) : ∫ x, projMean μ h x ∂μ = 0 := by
  by_cases hi : Integrable h μ
  · simp only [projMean, pair]
    rw [integral_sub hi (integrable_const _), integral_const]
    simp
  · have h0 : ∫ x, h x ∂μ = 0 := integral_undef hi
    simp only [projMean, pair, h0, sub_zero]

theorem sed_B15b_ae_unique_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ r : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hr : Torus.IsSmooth r)
    (hresp : ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
      projMean (withDensityReal ρ) φ x) :
    r =ᵐ[withDensityReal ρ] responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  obtain ⟨Λ₀, hΛ₀⟩ := b15b_bound (b15b_continuous hρ.smooth)
  have hΛ : ∀ x, ρ x ≤ Λ₀ := fun x => by
    have h := hΛ₀ x
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hcφ : Continuous φ := b15b_continuous hφ
  have hmemφ : MemLp φ 2 (withDensityReal ρ) := b15b_memLp hcφ _
  have hcr : Continuous r := b15b_continuous hr
  have hmemr : MemLp r 2 (withDensityReal ρ) := b15b_memLp hcr _
  have hri : Integrable r (withDensityReal ρ) := b15b_integrable hcr _
  have hfi : Integrable (projMean (withDensityReal ρ) φ) (withDensityReal ρ) := by
    apply b15b_integrable _ _
    show Continuous (fun x => φ x - pair (withDensityReal ρ) φ)
    exact hcφ.sub continuous_const
  have hβK : Integrable (fun x => β * Kop (periodicRiesz d s) (withDensityReal ρ) r x)
      (withDensityReal ρ) := by
    have e : (fun x => β * Kop (periodicRiesz d s) (withDensityReal ρ) r x) =
        fun x => projMean (withDensityReal ρ) φ x - r x := by
      funext x
      linarith [hresp x]
    rw [e]
    exact hfi.sub hri
  have hK0 : ∫ x, Kop (periodicRiesz d s) (withDensityReal ρ) r x ∂(withDensityReal ρ) = 0 :=
    b15b_projMean_integral_zero (withDensityReal ρ)
      (fun x => ∫ y, periodicRiesz d s (x - y) * r y ∂(withDensityReal ρ))
  have hf0 : ∫ x, projMean (withDensityReal ρ) φ x ∂(withDensityReal ρ) = 0 :=
    b15b_projMean_integral_zero (withDensityReal ρ) φ
  have hrmean : ∫ x, r x ∂(withDensityReal ρ) = 0 := by
    have e : ∫ x, r x ∂(withDensityReal ρ) =
        ∫ x, (projMean (withDensityReal ρ) φ x - β * Kop (periodicRiesz d s) (withDensityReal ρ) r x)
          ∂(withDensityReal ρ) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by linarith [hresp x])
    rw [e, integral_sub hfi hβK, integral_const_mul, hK0, hf0]
    ring
  have hrresp : HRS.IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ r :=
    ⟨hmemr, hrmean, Filter.Eventually.of_forall hresp⟩
  have hex : ∃ h, HRS.IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ h := ⟨r, hrresp⟩
  obtain ⟨h₀, -, huniq⟩ :=
    HRS.exists_unique_response hd hs0 hsd ρ hρ.density Λ₀ hΛ β hβ φ hmemφ
  have hchoose := hex.choose_spec
  unfold responseInverse
  rw [dif_pos hex]
  exact (huniq r hrresp).trans (huniq _ hchoose).symm

end HRS.MC.SEdge.B15b

end

