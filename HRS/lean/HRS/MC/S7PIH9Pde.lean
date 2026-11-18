import HRS.MC.S7PIH8Est

/-!
# Packet piH, part 9: `s7_PIH_heat_pde` (backward heat equation for the finite Gaussian heat function)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

/-- Averages of a continuous function over short intervals around `r` are close to its value at `r`. -/
theorem S7PIH_avg_close {A : ℝ → ℝ} {a b : ℝ} (hA : ContinuousOn A (Set.Icc a b)) {r : ℝ}
    (hr : r ∈ Set.Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ lo hi : ℝ, a ≤ lo → hi ≤ b → lo < hi → lo ≤ r → r ≤ hi → hi - lo < η →
      |(∫ v in Set.Ioc lo hi, A v) / (hi - lo) - A r| ≤ ε := by
  have h := hA r hr
  rw [Metric.continuousWithinAt_iff] at h
  obtain ⟨η, hη, h⟩ := h ε hε
  refine ⟨η, hη, fun lo hi hlo hhi hlh hlr hrh hw => ?_⟩
  have hsub : Set.Ioc lo hi ⊆ Set.Icc a b := fun v hv => ⟨hlo.trans hv.1.le, hv.2.trans hhi⟩
  have hint : IntegrableOn A (Set.Ioc lo hi) := (hA.integrableOn_Icc).mono_set hsub
  have hwpos : 0 < hi - lo := sub_pos.2 hlh
  have e : (∫ v in Set.Ioc lo hi, A v) / (hi - lo) - A r =
      (∫ v in Set.Ioc lo hi, (A v - A r)) / (hi - lo) := by
    rw [integral_sub hint (integrableOn_const (by simp)), setIntegral_const]
    simp [Real.volume_Ioc, hlh.le]
    field_simp
  rw [e, abs_div, abs_of_pos hwpos, div_le_iff₀ hwpos]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc lo hi)
    (f := fun v => A v - A r) (C := ε) (by simp) (fun v hv => by
      rw [Real.norm_eq_abs]
      have hv' := hsub hv
      have := h hv' (by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hv.1, hv.2])
      rw [Real.dist_eq] at this
      exact this.le)
  rw [Real.norm_eq_abs] at this
  simpa [Real.volume_Ioc, hlh.le, mul_comm] using this

end HRS.MC.Sec7.S7PIH

end
