import HRS.Main.T25PAux5
import HRS.Main.T25Aux7

/-!
# T25P, part 6: `‖Ψ_a‖_{L²} ≤ C J_N/√N` (the `L²` remainder bound for the `W₂` clause)

Cauchy-Schwarz twice (first in time with the weight `w_a`, then over the modes with the weights `⟨j⟩^{-(m-2)}`; this needs
exactly `m > d + 2`), and `t25_moving_pair_moments` (`r = 2`) for the second moments of the mode forcings.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- Cauchy-Schwarz for `ℝ≥0∞`-valued functions. -/
theorem t25p_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two) hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        have h' : ∫⁻ a, f a * g a ∂μ ≤ (∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
          simpa using h
        exact pow_le_pow_left' h' 2
    _ = (∫⁻ a, f a ^ 2 ∂μ) * (∫⁻ a, g a ^ 2 ∂μ) := by
        have key : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ 2 = x := fun x => by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        rw [mul_pow, key, key]

/-- Time Cauchy-Schwarz: `(∫ w |y|)² ≤ (∫ w) (∫ w |y|²)`. -/
theorem t25p_cs_time (μ : Measure ℝ) {w : ℝ → ℝ} (hw : Measurable w) (hw0 : ∀ r, 0 ≤ w r) {y : ℝ → ℝ}
    (hy : AEMeasurable y μ) :
    (∫⁻ r, ENNReal.ofReal (w r) * ‖y r‖ₑ ∂μ) ^ 2 ≤
      (∫⁻ r, ENNReal.ofReal (w r) ∂μ) * ∫⁻ r, ENNReal.ofReal (w r) * ‖y r‖ₑ ^ 2 ∂μ := by
  have hsq : Measurable fun r => ENNReal.ofReal (Real.sqrt (w r)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hw)
  have hf : AEMeasurable (fun r => ENNReal.ofReal (Real.sqrt (w r))) μ := hsq.aemeasurable
  have hg : AEMeasurable (fun r => ENNReal.ofReal (Real.sqrt (w r)) * ‖y r‖ₑ) μ := hf.mul hy.enorm
  have h := t25p_cs μ hf hg
  have e1 : ∀ r, ENNReal.ofReal (Real.sqrt (w r)) * (ENNReal.ofReal (Real.sqrt (w r)) * ‖y r‖ₑ) =
      ENNReal.ofReal (w r) * ‖y r‖ₑ := by
    intro r
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt (hw0 r)]
  have e2 : ∀ r, ENNReal.ofReal (Real.sqrt (w r)) ^ 2 = ENNReal.ofReal (w r) := by
    intro r
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hw0 r)]
  have e3 : ∀ r, (ENNReal.ofReal (Real.sqrt (w r)) * ‖y r‖ₑ) ^ 2 = ENNReal.ofReal (w r) * ‖y r‖ₑ ^ 2 := by
    intro r
    rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  exact h

/-- Measurability of a single time section. -/
theorem t25p_y_meas_omega (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {T' : ℝ} (hT' : 0 < T')
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → Config d N} (hX : IsProgressive ℱ (ofNNRealTime X)) (j : NonzeroLattice d)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') : Measurable (fun ω => t25p_y d s ρ X j r ω) := by
  have h : Measurable (fun ω : Ω => t25p_y d s ρ X j (clampTI T' r) ω) :=
    Measurable.comp (g := fun p : ℝ × Ω => t25p_y d s ρ X j (clampTI T' p.1) p.2)
      (f := fun ω : Ω => (r, ω)) (t25p_y_joint_meas hd htr hT' hX j) ((measurable_const (a := r)).prodMk measurable_id)
  have e : (fun ω => t25p_y d s ρ X j (clampTI T' r) ω) = fun ω => t25p_y d s ρ X j r ω := by
    funext ω; rw [clampTI_of_mem hr]
  rw [← e]
  exact h

end HRS.T25P
