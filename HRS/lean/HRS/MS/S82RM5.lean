import HRS.MS.S82RM4

/-!
# S8.2 R02 (S82R), M5: the one-site step of the weighted Lipschitz transfer
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_Hyp.Γu {μ : Measure E} {Γ : E → E → ℝ} {b : E → ℝ} {κ κ' : Fin n → (Fin n → E) → E → ℝ}
    (h : s82r_Hyp μ Γ b κ κ') (u : E) : Measurable (fun z => Γ z u) :=
  h.Γm.comp (measurable_id.prodMk measurable_const)

/-- `∫ w |κ - κ'| ≤ ∫ w b + Σ_ℓ ...` -/
lemma s82r_wdiff_bound {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ} {b : E → ℝ}
    {κ κ' : Fin n → (Fin n → E) → E → ℝ} (h : s82r_Hyp μ Γ b κ κ') {w : E → ℝ}
    (hwm : Measurable w) (hw0 : ∀ z, 0 ≤ w z) {Bw : ℝ} (hwb : ∀ z, w z ≤ Bw)
    (i : Fin n) (x y : Fin n → E)
    (hki : Integrable (fun z => |κ i x z - κ' i y z|) μ) :
    ∫ z, w z * |κ i x z - κ' i y z| ∂μ ≤ ∫ z, w z * b z ∂μ +
      ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
        s82r_Gam μ Γ w (x ℓ) + s82r_Gam μ Γ w (y ℓ) := by
  obtain ⟨G0, hG0⟩ := h.Γb
  obtain ⟨Bb, hBb⟩ := h.bb
  have hwΓ : ∀ u, Integrable (fun z => w z * Γ z u) μ := fun u =>
    Integrable.of_bound (hwm.mul (h.Γu u)).aestronglyMeasurable (Bw * G0)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 z) (h.Γ0 z u))]
        exact mul_le_mul (hwb z) (hG0 z u) (h.Γ0 z u) ((hw0 z).trans (hwb z)))
  have hwb' : Integrable (fun z => w z * b z) μ :=
    Integrable.of_bound (hwm.mul h.bm).aestronglyMeasurable (Bw * Bb)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 z) (h.b0 z))]
        exact mul_le_mul (hwb z) (hBb z) (h.b0 z) ((hw0 z).trans (hwb z)))
  have hT : ∀ ℓ ∈ Finset.univ.erase i, Integrable (fun z => w z * (if x ℓ = y ℓ then 0 else
      Γ z (x ℓ) + Γ z (y ℓ))) μ := by
    intro ℓ _
    by_cases hℓ : x ℓ = y ℓ
    · simp [hℓ]
    · simp only [hℓ, if_false]
      have := (hwΓ (x ℓ)).add (hwΓ (y ℓ))
      exact this.congr (ae_of_all _ fun z => by simp only [Pi.add_apply]; ring)
  have hsum : Integrable (fun z => w z * ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
      Γ z (x ℓ) + Γ z (y ℓ)) μ := by
    have := integrable_finset_sum _ hT
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [Finset.mul_sum]
  calc ∫ z, w z * |κ i x z - κ' i y z| ∂μ
      ≤ ∫ z, (w z * b z + w z * ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
          Γ z (x ℓ) + Γ z (y ℓ)) ∂μ := by
        refine integral_mono_of_nonneg (ae_of_all _ fun z => mul_nonneg (hw0 z) (abs_nonneg _))
          (hwb'.add hsum) (ae_of_all _ fun z => ?_)
        show w z * |κ i x z - κ' i y z| ≤ w z * b z + w z * ∑ ℓ ∈ Finset.univ.erase i,
          if x ℓ = y ℓ then 0 else Γ z (x ℓ) + Γ z (y ℓ)
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (h.D i x y z) (hw0 z)
    _ = ∫ z, w z * b z ∂μ + ∑ ℓ ∈ Finset.univ.erase i, ∫ z, w z * (if x ℓ = y ℓ then 0 else
          Γ z (x ℓ) + Γ z (y ℓ)) ∂μ := by
        rw [integral_add hwb' hsum, ← integral_finset_sum _ hT]
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [Finset.mul_sum]
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        by_cases hℓ : x ℓ = y ℓ
        · simp [hℓ]
        · simp only [hℓ, if_false]
          unfold s82r_Gam
          rw [← integral_add (hwΓ (x ℓ)) (hwΓ (y ℓ))]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          ring

end HRS.MS.S82R

end
