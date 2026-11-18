import HRS.MS.S82RM11

/-!
# S8.2 R02 (S82R), M12: iterates of the scan operator and the transfer along the iteration
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_Hyp.symm {μ : Measure E} {Γ : E → E → ℝ} {b : E → ℝ}
    {κ κ' : Fin n → (Fin n → E) → E → ℝ} (h : s82r_Hyp μ Γ b κ κ') : s82r_Hyp μ Γ b κ' κ where
  Γm := h.Γm
  Γ0 := h.Γ0
  Γb := h.Γb
  bm := h.bm
  b0 := h.b0
  bb := h.bb
  D := fun i x y z => by
    have := h.D i y x z
    rw [abs_sub_comm]
    refine this.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hℓ : x ℓ = y ℓ
    · simp [hℓ, eq_comm]
    · have : ¬ y ℓ = x ℓ := fun h' => hℓ h'.symm
      simp only [hℓ, this, if_false]; ring

lemma s82r_iter_scan [NeZero n] (S : Spec E n) {f : (Fin n → E) → ℝ} (hfm : Measurable f)
    (hfb : ∀ x, |f x| ≤ 1) (J : ℕ) :
    Measurable (S.scan^[J] f) ∧ (∀ x, |(S.scan^[J] f) x| ≤ 1) ∧
      ∫ x, (S.scan^[J] f) x ∂S.P = ∫ x, f x ∂S.P := by
  induction J with
  | zero => exact ⟨hfm, hfb, rfl⟩
  | succ J ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [Function.iterate_succ_apply']
      exact ⟨Spec.measurable_scan h1, fun x => Spec.abs_scan_le h2 x, by
        rw [Spec.integral_scan h1 h2, h3]⟩

end HRS.MS.S82R

end
