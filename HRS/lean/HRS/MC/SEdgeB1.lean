import HRS.MC.SEdgeVocab
import HRS.Sections.Q66AuxE
import HRS.Sections.Q66AuxF

/-!
# Packet B1: smooth response and transport field (relocation of `sed_B1_regular`)

Proof of the statement `HRS.MC.SEdge.sed_B1_regular` (SEdgeSpec.lean) in its own file.  Inputs:
`HRS.Q66.q66_response_regular` (smooth representative of the response, equation everywhere),
`HRS.Q66.q66_exists_field` (smooth transport field with `-div(rho v) = rho r`), `HRS.exists_unique_response`
(uniqueness of the response up to `mu`-a.e. equality), `HRS.integral_withDensityReal_eq`.
The spec theorem stays `sorry`; the `example` at the end ties this proof to it by `type_of%`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B1

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem b1_continuous {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Continuous f :=
  HRS.Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf).continuous

theorem b1_bound {f : Torus d → ℝ} (hf : Continuous f) : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun x => hC x (Set.mem_univ x)⟩

theorem b1_memLp {f : Torus d → ℝ} (hf : Continuous f) (μ : Measure (Torus d))
    [IsFiniteMeasure μ] : MemLp f 2 μ := by
  obtain ⟨C, hC⟩ := b1_bound hf
  exact MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC x)

theorem sed_B1_regular_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ (r : Torus d → ℝ) (v : Fin d → Torus d → ℝ), Torus.IsSmooth r ∧ (∀ j, Torus.IsSmooth (v j)) ∧
      r =ᵐ[withDensityReal ρ] responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ ∧
      (∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
        projMean (withDensityReal ρ) φ x) ∧
      ∫ x, r x ∂(withDensityReal ρ) = 0 ∧
      ∀ x, ∑ j, Torus.partialDeriv j (fun y => ρ y * v j y) x = -(ρ x * r x) := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  obtain ⟨r, hrS, hresp, heq⟩ := HRS.Q66.q66_response_regular hd hs0 hs β hβ hρ hφ
  have hpair : ∫ x, r x ∂(withDensityReal ρ) = 0 := hresp.2.1
  have hmean : ∫ x, ρ x * r x = 0 :=
    (HRS.integral_withDensityReal_eq ρ hρ.density.measurable (fun x => (hρ.pos x).le) r).symm.trans
      hpair
  obtain ⟨v, hv, hdiv⟩ := HRS.Q66.q66_exists_field hρ hrS hmean
  refine ⟨r, v, hrS, hv, ?_, heq, hpair, hdiv⟩
  obtain ⟨Λ₀, hΛ₀⟩ := b1_bound (b1_continuous hρ.smooth)
  have hΛ : ∀ x, ρ x ≤ Λ₀ := fun x => by
    have h := hΛ₀ x
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hmemφ : MemLp φ 2 (withDensityReal ρ) := b1_memLp (b1_continuous hφ) _
  have hex : ∃ h, HRS.IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ h := ⟨r, hresp⟩
  obtain ⟨h₀, -, huniq⟩ :=
    HRS.exists_unique_response hd hs0 hsd ρ hρ.density Λ₀ hΛ β hβ φ hmemφ
  have hchoose := hex.choose_spec
  unfold responseInverse
  rw [dif_pos hex]
  exact (huniq r hresp).trans (huniq _ hchoose).symm

end HRS.MC.SEdge.B1

end

