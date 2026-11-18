import HRS.Commutator.Torus.LEIBTAux2
import HRS.Commutator.Whole.XLIAux44

/-!
# LEIB-T helpers, part 3: decay of the inverse Fourier transform in terms of Schwartz seminorms
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The inverse Fourier transform on Schwartz space as a continuous linear map. -/
def leibt_invFCLM : SchwartzMap 𝔼 ℂ →L[ℂ] SchwartzMap 𝔼 ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := 𝔼))) ∘L
    (SchwartzMap.fourierTransformCLM ℂ)

lemma leibt_invFCLM_apply (ρ : SchwartzMap 𝔼 ℂ) : leibt_invFCLM ρ = 𝓕⁻ ρ := rfl

lemma leibt_invF_decay (K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (ρ : SchwartzMap 𝔼 ℂ) (w : 𝔼),
      (1 + ‖w‖) ^ K * ‖(𝓕⁻ ρ : SchwartzMap 𝔼 ℂ) w‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ρ := by
  set q0 : Seminorm ℂ (SchwartzMap 𝔼 ℂ) := (Finset.Iic (K, 0)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ)
  set q : Seminorm ℂ (SchwartzMap 𝔼 ℂ) := q0.comp ((leibt_invFCLM (d := d)) : SchwartzMap 𝔼 ℂ →ₗ[ℂ] SchwartzMap 𝔼 ℂ)
  have hq : Continuous q := by
    have h0 : Continuous q0 := Seminorm.continuous_finsetSup fun i _ =>
      (schwartz_withSeminorms ℂ 𝔼 ℂ).continuous_seminorm i
    exact h0.comp (leibt_invFCLM (d := d)).continuous
  obtain ⟨s, C, hC0, hqC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ 𝔼 ℂ) q hq
  refine ⟨s, 2 ^ K * (C : ℝ), by positivity, fun ρ w => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, 0)) (k := K) (n := 0)
    le_rfl le_rfl (𝓕⁻ ρ : SchwartzMap 𝔼 ℂ) w
  have h2 : (Finset.Iic (K, 0)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ) (𝓕⁻ ρ : SchwartzMap 𝔼 ℂ)
      ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ρ := by
    have := hqC ρ
    exact this
  simp only [norm_iteratedFDeriv_zero] at h1
  calc (1 + ‖w‖) ^ K * ‖(𝓕⁻ ρ : SchwartzMap 𝔼 ℂ) w‖
      ≤ 2 ^ K * (Finset.Iic (K, 0)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ) (𝓕⁻ ρ : SchwartzMap 𝔼 ℂ) := h1
    _ ≤ 2 ^ K * ((C : ℝ) * (s.sup (schwartzSeminormFamily ℂ 𝔼 ℂ)) ρ) := by gcongr
    _ = _ := by ring

end HRS.Commutator.TorusNote
