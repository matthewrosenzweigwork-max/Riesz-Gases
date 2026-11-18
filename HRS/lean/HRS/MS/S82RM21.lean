import HRS.MS.S82RM20
import HRS.MS.S82RM14

/-!
# S8.2 R02 (S82R), M21: the field specifications satisfy the transfer hypotheses
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

/-- the one-site conditional density of the field ensemble -/
def s82r_kap {μ : Measure E} (V : WeakPotential μ) (ψ : E → ℝ) (lam : ℝ) {n : ℕ} (i : Fin n)
    (x : Fin n → E) (z : E) : ℝ := s82r_nd μ (s82r_PhiC V ψ lam i x) z

lemma s82r_kap_dens {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ : E → ℝ}
    {M M₁ lam : ℝ} (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    s82r_Dens μ (fieldSpec (V := V) hψ hlam n) (s82r_kap V ψ lam) where
  eq := fun i x => by
    have := siteKernel_fieldDensity (V := V) hψ hlam i x
    rw [fieldSpec_G]
    rw [this]
    rfl
  nonneg := fun i x z => by
    unfold s82r_kap s82r_nd
    exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun y => (Real.exp_pos _).le)
  meas := fun i x => by
    unfold s82r_kap s82r_nd
    refine (Real.measurable_exp.comp ?_).div_const _
    exact hψ.measurable.sub ((Finset.measurable_sum _ fun l _ =>
      V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul lam)

lemma s82r_fld_isField {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {ψ : E → ℝ}
    {M M₁ : ℝ} (hψ : IsField μ ψ M M₁) {m : ℕ} (p : Fin m → E) (t : Fin m → ℝ) (ht : ∀ ℓ, 0 ≤ t ℓ)
    (s : Finset (Fin m)) :
    IsField μ (s82r_Fld V p t s ψ) M (M₁ + (∑ ℓ ∈ s, t ℓ) * V.γ) := by
  have hqi : ∀ w : E, Integrable (fun z => V.q z w) μ := integrable_q_left V
  have hS1 : Integrable (fun z => ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ)) μ :=
    integrable_finset_sum _ fun ℓ _ => (hqi (p ℓ)).const_mul _
  refine ⟨?_, fun z => ?_, hψ.integrable.sub hS1, ?_⟩
  · exact hψ.measurable.sub (Finset.measurable_sum _ fun ℓ _ =>
      (V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul _)
  · have : 0 ≤ ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) :=
      Finset.sum_nonneg fun ℓ _ => mul_nonneg (ht ℓ) (V.q_nonneg _ _)
    unfold s82r_Fld; linarith [hψ.le z]
  · unfold s82r_Fld
    rw [integral_sub hψ.integrable hS1]
    have b1 : ∫ z, ∑ ℓ ∈ s, t ℓ * V.q z (p ℓ) ∂μ ≤ (∑ ℓ ∈ s, t ℓ) * V.γ := by
      rw [integral_finset_sum _ fun ℓ _ => (hqi (p ℓ)).const_mul _, Finset.sum_mul]
      refine Finset.sum_le_sum fun ℓ _ => ?_
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (integral_q_left_le V _) (ht ℓ)
    have := hψ.ge
    linarith

end HRS.MS.S82R

end
