import HRS.MC.SEdgeVocab

/-!
# Packet B15a: bridge `sed_Cmat = susceptibilityCov` (relocation of `sed_B15a_bridge_cov`)

Proof of the statement `HRS.MC.SEdge.sed_B15a_bridge_cov` (SEdgeSpec.lean) in its own file.  The spec theorem
stays `sorry`; the `example` at the end ties this proof to it by `type_of%`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B15a

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem b15a_continuous {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  HRS.Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf).continuous

theorem b15a_bound {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn (b15a_continuous hf).continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

/-- Existence of the response (`exists_unique_response`) for a smooth test function. -/
theorem b15a_resp_exists (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    ∃ h, HRS.IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  obtain ⟨Λ₀, hΛ₀⟩ := b15a_bound hρ.smooth
  have hΛ : ∀ x, ρ x ≤ Λ₀ := fun x => by
    have h := hΛ₀ x
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  obtain ⟨Cψ, hCψ⟩ := b15a_bound hψ
  have hmem : MemLp ψ 2 (withDensityReal ρ) :=
    MemLp.of_bound (b15a_continuous hψ).aestronglyMeasurable Cψ
      (Filter.Eventually.of_forall fun x => hCψ x)
  obtain ⟨h, hh, -⟩ := HRS.exists_unique_response hd hs0 hsd ρ hρ.density Λ₀ hΛ β hβ ψ hmem
  exact ⟨h, hh⟩

theorem b15a_resp_eq {ρ : Torus d → ℝ} (β : ℝ) {ψ : Torus d → ℝ} (s : ℝ)
    (hex : ∃ h, HRS.IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h) :
    responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ = hex.choose := by
  unfold responseInverse
  rw [dif_pos hex]

theorem b15a_entry (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    ∫ x, φ x * responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ x ∂(withDensityReal ρ) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ ψ := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  have hex := b15a_resp_exists hd hs0 hs hβ hρ hψ
  have hRe := b15a_resp_eq β s hex
  have hspec := hex.choose_spec
  have hmemR : MemLp hex.choose 2 (withDensityReal ρ) := hspec.1
  have hintR : Integrable hex.choose (withDensityReal ρ) := hmemR.integrable one_le_two
  have hmeanR : ∫ x, hex.choose x ∂(withDensityReal ρ) = 0 := hspec.2.1
  obtain ⟨Cφ, hCφ⟩ := b15a_bound hφ
  have hintφR : Integrable (fun x => φ x * hex.choose x) (withDensityReal ρ) :=
    hintR.bdd_mul (b15a_continuous hφ).aestronglyMeasurable (Filter.Eventually.of_forall hCφ)
  simp only [susceptibilityCov, l2Inner, projMean, hRe]
  have h1 : (fun x => (φ x - pair (withDensityReal ρ) φ) * hex.choose x) =
      fun x => φ x * hex.choose x - pair (withDensityReal ρ) φ * hex.choose x := by
    funext x; ring
  rw [h1, integral_sub hintφR (hintR.const_mul _), integral_const_mul, hmeanR, mul_zero, sub_zero]

theorem sed_B15a_bridge_cov_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (∀ a b, sed_Cmat d s β ρ φ a b =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (φ a) (φ b)) ∧
    ∀ b, ∫ x, responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b) x
      ∂(withDensityReal ρ) = 0 := by
  refine ⟨fun a b => ?_, fun b => ?_⟩
  · exact b15a_entry hd hs0 hs hβ hρ (hφ a) (hφ b)
  · haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
    have hex := b15a_resp_exists hd hs0 hs hβ hρ (hφ b)
    rw [b15a_resp_eq β s hex]
    exact hex.choose_spec.2.1

end HRS.MC.SEdge.B15a

end

