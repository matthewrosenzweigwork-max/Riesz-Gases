import HRS.MS.S21E_Trilin

/-!
# S2.1(iii) packet G12: the initial tensor `κ₀ = ∫ v(x)^{⊗3} dμ₀(x)` (generic Banach space)

`κ₀ = E[v ⊗ v ⊗ v]` for a strongly measurable `v : E → B` with `∫ ‖v‖³ < ∞` (in the paper `v = ℓ^b_x`, the transported response vector, `B = 𝒳`): it lies in
`projTensor B 3`, is symmetric (an integral of cubes), has norm `≤ ∫ ‖v‖³`, and on a product of functionals `κ₀(ℓ₀⊗ℓ₁⊗ℓ₂) = ∫ ∏ ℓ_i(v x) dμ₀`
(the identification `ℓ_i(v x) = r_i(x)` is the open packet H4).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

namespace HRS.MS.S21E

open HRS HRS.MC.E213T HRS.MC.E213U18

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]

/-- The initial tensor. -/
def s21eKappa0 (v : E → B) : TensorDual B 3 := bochTensor3 μ v v v

theorem s21e_kappa0_mem {v : E → B} (hv : AEStronglyMeasurable v μ)
    (hi : Integrable (fun x => ‖v x‖ * ‖v x‖ * ‖v x‖) μ) : s21eKappa0 μ v ∈ projTensor B 3 :=
  bochTensor3_mem hv hv hv hi

theorem s21e_kappa0_norm_le {v : E → B} (hv : AEStronglyMeasurable v μ)
    (hi : Integrable (fun x => ‖v x‖ * ‖v x‖ * ‖v x‖) μ) :
    ‖s21eKappa0 μ v‖ ≤ ∫ x, ‖v x‖ * ‖v x‖ * ‖v x‖ ∂μ :=
  norm_bochTensor3_le hv hv hv hi

theorem s21e_kappa0_apply {v : E → B} (hv : AEStronglyMeasurable v μ)
    (hi : Integrable (fun x => ‖v x‖ * ‖v x‖ * ‖v x‖) μ) (M : B [×3]→L[ℝ] ℝ) :
    s21eKappa0 μ v M = ∫ x, M ![v x, v x, v x] ∂μ :=
  bochTensor3_apply hv hv hv hi M

theorem s21e_kappa0_symm {v : E → B} (hv : AEStronglyMeasurable v μ)
    (hi : Integrable (fun x => ‖v x‖ * ‖v x‖ * ‖v x‖) μ) (σ : Equiv.Perm (Fin 3)) (M : B [×3]→L[ℝ] ℝ) :
    s21eKappa0 μ v (M.domDomCongr σ) = s21eKappa0 μ v M := by
  rw [s21e_kappa0_apply μ hv hi, s21e_kappa0_apply μ hv hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hc : ∀ k : Fin 3, (![v x, v x, v x] : Fin 3 → B) k = v x := fun k => by fin_cases k <;> rfl
  have h : (![v x, v x, v x] : Fin 3 → B) ∘ σ = ![v x, v x, v x] := by
    funext j
    rw [Function.comp_apply, hc, hc]
  show M ((![v x, v x, v x] : Fin 3 → B) ∘ σ) = M ![v x, v x, v x]
  rw [h]

theorem s21e_kappa0_trilin {v : E → B} (hv : AEStronglyMeasurable v μ)
    (hi : Integrable (fun x => ‖v x‖ * ‖v x‖ * ‖v x‖) μ) (ℓ : Fin 3 → B →L[ℝ] ℝ) :
    s21eKappa0 μ v (trilin ℓ) = ∫ x, ℓ 0 (v x) * ℓ 1 (v x) * ℓ 2 (v x) ∂μ := by
  rw [s21e_kappa0_apply μ hv hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [trilin_apply]

end HRS.MS.S21E
