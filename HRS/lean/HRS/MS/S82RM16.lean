import HRS.MS.S82RM15

/-!
# S8.2 R02 (S82R), M16: one-change and pin-addition stability of the one-site density
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E]

lemma s82r_oc_coord {μ : Measure E} [IsProbabilityMeasure μ] (V : WeakPotential μ) {Ψ : E → ℝ}
    (hΨm : Measurable Ψ) {M M2 : ℝ} (hΨM : ∀ z, Ψ z ≤ M) {c : ℝ} (hc : 0 ≤ c) (u u' : E)
    (hi₁ : Integrable (fun z => Ψ z - c * V.q z u) μ) (hi₂ : Integrable (fun z => Ψ z - c * V.q z u') μ)
    (h₁ : -M2 ≤ ∫ z, (Ψ z - c * V.q z u) ∂μ) (h₂ : -M2 ≤ ∫ z, (Ψ z - c * V.q z u') ∂μ) (z : E) :
    |s82r_nd μ (fun z => Ψ z - c * V.q z u) z - s82r_nd μ (fun z => Ψ z - c * V.q z u') z| ≤
      Real.exp (M2 + M) * (s82r_d V c z u + s82r_d V c z u') +
        Real.exp (M + 2 * M2 + M) * (2 * (c * V.γ)) := by
  have hm : ∀ w : E, Measurable (fun z => Ψ z - c * V.q z w) := fun w =>
    hΨm.sub ((V.measurable_q.comp (measurable_id.prodMk measurable_const)).const_mul c)
  have hM : ∀ w z, Ψ z - c * V.q z w ≤ M := fun w z => by
    have := mul_nonneg hc (V.q_nonneg z w); linarith [hΨM z]
  have hd := s82r_nd_diff μ (hm u) (hm u') hi₁ hi₂ (hM u) (hM u') h₁ h₂ z
  have hΔ : ∀ y, |Real.exp (Ψ y - c * V.q y u) - Real.exp (Ψ y - c * V.q y u')| ≤
      Real.exp M * (s82r_d V c y u + s82r_d V c y u') := by
    intro y
    have e : Real.exp (Ψ y - c * V.q y u) - Real.exp (Ψ y - c * V.q y u') =
        Real.exp (Ψ y) * (Real.exp (-(c * V.q y u)) - Real.exp (-(c * V.q y u'))) := by
      have e1 : ∀ w, Real.exp (Ψ y - c * V.q y w) = Real.exp (Ψ y) * Real.exp (-(c * V.q y w)) := by
        intro w; rw [← Real.exp_add]; ring_nf
      rw [e1 u, e1 u']; ring
    rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (Real.exp_le_exp.2 (hΨM y)) (s82r_exp_diff_le V hc y u u')
      (abs_nonneg _) (Real.exp_pos _).le
  have hint : ∫ y, |Real.exp (Ψ y - c * V.q y u) - Real.exp (Ψ y - c * V.q y u')| ∂μ ≤
      Real.exp M * (2 * (c * V.γ)) := by
    have hdi : ∀ w, Integrable (fun y => s82r_d V c y w) μ := fun w =>
      Integrable.of_bound (s82r_d_meas V c w).aestronglyMeasurable 1 (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (s82r_d_nonneg V hc z w)]; exact s82r_d_lt_one V c z w)
    calc ∫ y, |Real.exp (Ψ y - c * V.q y u) - Real.exp (Ψ y - c * V.q y u')| ∂μ
        ≤ ∫ y, Real.exp M * (s82r_d V c y u + s82r_d V c y u') ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
            (((hdi u).add (hdi u')).const_mul _) (ae_of_all _ hΔ)
      _ = Real.exp M * (∫ y, s82r_d V c y u ∂μ + ∫ y, s82r_d V c y u' ∂μ) := by
          rw [integral_const_mul, integral_add (hdi u) (hdi u')]
      _ ≤ Real.exp M * (2 * (c * V.γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          linarith [s82r_d_int V hc u, s82r_d_int V hc u']
  refine hd.trans (add_le_add ?_ ?_)
  · calc Real.exp M2 * |Real.exp (Ψ z - c * V.q z u) - Real.exp (Ψ z - c * V.q z u')|
        ≤ Real.exp M2 * (Real.exp M * (s82r_d V c z u + s82r_d V c z u')) :=
          mul_le_mul_of_nonneg_left (hΔ z) (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add]; ring
  · calc Real.exp (M + 2 * M2) * ∫ y, |Real.exp (Ψ y - c * V.q y u) - Real.exp (Ψ y - c * V.q y u')| ∂μ
        ≤ Real.exp (M + 2 * M2) * (Real.exp M * (2 * (c * V.γ))) :=
          mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
      _ = Real.exp (M + 2 * M2 + M) * (2 * (c * V.γ)) := by rw [Real.exp_add (M + 2 * M2) M]; ring

end HRS.MS.S82R

end
