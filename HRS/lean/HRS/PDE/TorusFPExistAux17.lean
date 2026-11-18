import HRS.PDE.TorusFPExistAux16

/-!
# D1 existence, helper 17: right derivative of `s ↦ ∫ f_s dμ_s` for `C^{1,2}` tests
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

section Deriv

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

theorem d1_continuous_of_isCk2 {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) : Continuous φ := by
  apply Torus.continuous_of_continuous_lift
  exact (d1_contDiff_of_isCk2 hφ (j := 0) (by norm_num)).continuous

/-- Right derivative of `t ↦ ∫ φ dμ_t` for `C²` time-independent `φ`. -/
theorem d1_hasDerivWithinAt_Ioi_C2 {φ : Torus n → ℝ} (hφ : Torus.IsCk 2 φ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (fun t => ∫ x, φ x ∂(d1_mu hn hκ hU μ₀ t))
      (∫ x, d1_gen κ (d1_gradDrift U) φ x ∂(d1_mu hn hκ hU μ₀ s)) (Set.Ioi s) s := by
  have hLφ : Continuous (d1_gen κ (d1_gradDrift U) φ) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hφ
  have hB := d1_narrow hn hκ hU μ₀ hLφ (s + 1)
  have hd := d1_hasDerivWithinAt_setIntegral hB (s := s) (T := s + 1) ⟨hs, by linarith⟩
  have hd' := hd.const_add (∫ x, φ x ∂μ₀)
  refine hd'.congr (fun t ht => ?_) ?_
  · have ht0 : 0 ≤ t := by have : s < t := ht; linarith
    exact d1_weak_C2 hn hκ hU μ₀ hφ ht0
  · exact d1_weak_C2 hn hκ hU μ₀ hφ hs

end Deriv

end HRS
