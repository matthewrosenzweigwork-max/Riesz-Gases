import HRS.MH.PairingRdDefs
import HRS.MH.PairingRdP4
import HRS.MP.RdGenConv

/-!
# PairingRd packet PR5 (`integrable_conv_rd`): integrability and uniform bound of the cancellation convolution

Statement copied verbatim from `HRS/MH/PairingRdSpec.lean`. Route: the integrand is dominated (PR4,
`conv_integrand_bound_rd`) by `σ (Λ 1_{‖x-y‖≤1/4} ‖x-y‖^(β-s-1) + 4^(s+1) |h y|)`, integrable by
`rg_near_integrable` (exponent `-(s+1-β) > -d`) and `Integrable h`; its integral does not depend on `x`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MH.PairingRdP

open HRS HRS.Duality HRS.MH.PairingRd

variable {d N : ℕ}

/-- **PR5** `integrable_conv_rd` (proof). -/
theorem integrable_conv_rd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ} {Λ β : ℝ}
    (hh : Measurable h) (hint : Integrable h) (hΛ : 0 ≤ Λ) (hβ : s + 1 - d < β)
    (hH : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Λ * ‖z‖ ^ β) :
    (∀ x, Integrable (convInt (Whole.rieszKernelGrad d s) h x)) ∧
      ∃ K : ℝ, ∀ x, ‖Whole.convGradConvW (Whole.rieszKernelGrad d s) h x‖ ≤ K := by
  set J : Euc d → ℝ := Set.indicator (Metric.closedBall (0 : Euc d) (1 / 4))
    (fun z => ‖z‖ ^ (β - s - 1)) with hJ
  have hJint : Integrable J := by
    rw [hJ, integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    have := HRS.MP.RdGen.rg_near_integrable (d := d) hd (s := s + 1 - β) (by linarith)
    refine this.congr_fun (fun z _ => ?_) Metric.isClosed_closedBall.measurableSet
    show ‖z‖ ^ (-(s + 1 - β)) = ‖z‖ ^ (β - s - 1)
    congr 1; ring
  set σ : ℝ := max 1 s with hσ
  have hσ0 : 0 ≤ σ := (zero_le_one).trans (le_max_left _ _)
  let m : Euc d → Euc d → ℝ := fun x y => σ * (Λ * J (x - y) + 4 ^ (s + 1) * |h y|)
  have hmint : ∀ x, Integrable (m x) := fun x => by
    have h1 : Integrable (fun y => J (x - y)) := hJint.comp_sub_left x
    exact (((h1.const_mul Λ).add (hint.abs.const_mul _))).const_mul σ
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hbd : ∀ x, ∀ᵐ y ∂(volume : Measure (Euc d)), ‖convInt (Whole.rieszKernelGrad d s) h x y‖ ≤ m x y := by
    intro x
    have hae : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x :=
      compl_mem_ae_iff.mpr (measure_singleton x)
    filter_upwards [hae] with y hy
    exact conv_integrand_bound_rd hs0 hΛ hH x y hy.symm
  have hmeas : ∀ x, AEStronglyMeasurable (convInt (Whole.rieszKernelGrad d s) h x) volume := by
    intro x
    have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) s
    have hsub : Measurable (fun y : Euc d => x - y) := measurable_const.sub measurable_id
    refine Measurable.aestronglyMeasurable ?_
    refine Measurable.ite (measurableSet_le (measurable_norm.comp hsub) measurable_const) ?_ ?_
    · exact (hh.sub measurable_const).smul (hG.comp hsub)
    · exact hh.smul (hG.comp hsub)
  have hI : ∀ x, ∫ y, m x y = σ * (Λ * (∫ z, J z) + 4 ^ (s + 1) * ∫ y, |h y|) := by
    intro x
    have h1 : Integrable (fun y => J (x - y)) := hJint.comp_sub_left x
    simp only [m]
    rw [integral_const_mul, integral_add (h1.const_mul Λ) (hint.abs.const_mul _), integral_const_mul,
      integral_const_mul, integral_sub_left_eq_self J volume x]
  refine ⟨fun x => Integrable.mono' (hmint x) (hmeas x) (hbd x), σ * (Λ * (∫ z, J z) + 4 ^ (s + 1) * ∫ y, |h y|), fun x => ?_⟩
  rw [← hI x]
  exact norm_integral_le_of_norm_le (hmint x) (hbd x)

end HRS.MH.PairingRdP
