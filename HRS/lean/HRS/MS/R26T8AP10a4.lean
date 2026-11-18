import HRS.MS.R26T8AP10a3

/-!
# S8.2 T8A P10a (part 4): combinators for Gaussian-times-pole majorants, measurability off a point
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p10a_gp_of_bound {y : Euc d} {τ : ℝ} {φ ψ : Euc d → ℝ} (hφ : R26P10GP y τ φ)
    {B : ℝ} (hB : 0 ≤ B) (hψ : ∀ u, u ≠ y → |ψ u| ≤ B * |φ u|) : R26P10GP y τ ψ := by
  obtain ⟨C, c, hC, hc, h⟩ := hφ
  refine ⟨B * C, c, mul_nonneg hB hC, hc, fun u hu => ?_⟩
  calc |ψ u| ≤ B * |φ u| := hψ u hu
    _ ≤ B * (C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))) :=
        mul_le_mul_of_nonneg_left (h u hu) hB
    _ = _ := by ring

theorem r26t8a_p10a_gp_mono {y : Euc d} {τ τ' : ℝ} {φ : Euc d → ℝ} (hφ : R26P10GP y τ φ)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ τ') : R26P10GP y τ' φ := by
  obtain ⟨C, c, hC, hc, h⟩ := hφ
  refine ⟨2 * C, c, by positivity, hc, fun u hu => ?_⟩
  have hn : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
  have h1 : 1 + ‖u - y‖ ^ (-τ) ≤ 2 * (1 + ‖u - y‖ ^ (-τ')) := by
    have hp : 0 ≤ ‖u - y‖ ^ (-τ') := Real.rpow_nonneg hn.le _
    by_cases hr : ‖u - y‖ ≤ 1
    · have := Real.rpow_le_rpow_of_exponent_ge hn hr (by linarith : -τ' ≤ -τ)
      nlinarith
    · have hr' : 1 ≤ ‖u - y‖ := (not_le.1 hr).le
      have := Real.rpow_le_one_of_one_le_of_nonpos hr' (by linarith : -τ ≤ 0)
      nlinarith [hp]
  refine (h u hu).trans ?_
  have hE : 0 ≤ C * Real.exp (-c * ‖u‖ ^ 2) := by positivity
  calc C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ))
      ≤ C * Real.exp (-c * ‖u‖ ^ 2) * (2 * (1 + ‖u - y‖ ^ (-τ'))) := mul_le_mul_of_nonneg_left h1 hE
    _ = _ := by ring

theorem r26t8a_p10a_gp_add {y : Euc d} {τ : ℝ} {φ ψ : Euc d → ℝ} (hφ : R26P10GP y τ φ)
    (hψ : R26P10GP y τ ψ) : R26P10GP y τ (fun u => φ u + ψ u) := by
  obtain ⟨C, c, hC, hc, h⟩ := hφ
  obtain ⟨C', c', hC', hc', h'⟩ := hψ
  refine ⟨C + C', min c c', by positivity, lt_min hc hc', fun u hu => ?_⟩
  have e1 : Real.exp (-c * ‖u‖ ^ 2) ≤ Real.exp (-min c c' * ‖u‖ ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left c c', sq_nonneg ‖u‖])
  have e2 : Real.exp (-c' * ‖u‖ ^ 2) ≤ Real.exp (-min c c' * ‖u‖ ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right c c', sq_nonneg ‖u‖])
  have hp : 0 ≤ 1 + ‖u - y‖ ^ (-τ) := by positivity
  calc |φ u + ψ u| ≤ |φ u| + |ψ u| := abs_add_le _ _
    _ ≤ C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ)) +
        C' * Real.exp (-c' * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ)) := add_le_add (h u hu) (h' u hu)
    _ ≤ (C + C') * Real.exp (-min c c' * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ)) := by
        have := mul_le_mul_of_nonneg_left e1 hC
        have := mul_le_mul_of_nonneg_left e2 hC'
        nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hC) hp,
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hC') hp]

/-- A function continuous off a point is a.e. strongly measurable (`d ≥ 1`). -/
theorem r26t8a_p10a_aesm (hd : 2 ≤ d) (y : Euc d) {φ : Euc d → ℝ} (hφ : ContinuousOn φ {y}ᶜ) :
    AEStronglyMeasurable φ volume := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hs : MeasurableSet ({y}ᶜ : Set (Euc d)) := (measurableSet_singleton y).compl
  have h1 : AEStronglyMeasurable φ (volume.restrict {y}ᶜ) := hφ.aestronglyMeasurable hs
  have h2 : (volume : Measure (Euc d)).restrict {y}ᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton y))
  rwa [h2] at h1

/-- A measurable function with a Gaussian-pole bound is integrable. -/
theorem r26t8a_p10a_gp_integrable (hd : 2 ≤ d) {y : Euc d} {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < d)
    {φ : Euc d → ℝ} (hφ : R26P10GP y τ φ) (hm : AEStronglyMeasurable φ volume) :
    Integrable φ := by
  obtain ⟨C, c, hC, hc, h⟩ := hφ
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  refine Integrable.mono' ((r26t8a_p10a_gp_dom hd hτ0 hτ y hc).const_mul C) hm ?_
  filter_upwards [hae] with u hu
  rw [Real.norm_eq_abs]
  calc |φ u| ≤ C * Real.exp (-c * ‖u‖ ^ 2) * (1 + ‖u - y‖ ^ (-τ)) := h u hu
    _ = _ := by ring

end HRS.MS.R26T8A
