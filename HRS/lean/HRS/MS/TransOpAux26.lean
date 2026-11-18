import HRS.MS.TransOpAux25
import HRS.MS.MovThermAux2

/-!
# S611 packet P5c: the constant thermal solution is an `IsResultingSolution` (`ε = 0`, `c₁ = C₁ = 1`), and an admissible `ψ` exists
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_memOsc_zero (M : ℝ) : MemOsc M (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨MeasureTheory.MemLp.zero, ?_⟩
  have : ∀ α : MultiIndex d, hermiteCoeff (fun _ : Euc d => (0 : ℝ)) α = 0 := fun α => by
    simp [hermiteCoeff]
  simp [this]

theorem s611_oscNorm_zero (M : ℝ) : oscNorm M (fun _ : Euc d => (0 : ℝ)) = 0 := by
  have : ∀ α : MultiIndex d, hermiteCoeff (fun _ : Euc d => (0 : ℝ)) α = 0 := fun α => by
    simp [hermiteCoeff]
  simp [oscNorm, this]

theorem s611_resulting_const (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) {εstar : ℝ} (hε : 0 < εstar)
    (ψ : Euc d → ℝ) :
    IsResultingSolution d s q β ρ₀ εstar 0 ψ 1 1 (fun _ => ρ₀) := by
  have hzero : (fun x => (ρ₀ x - ρ₀ x) / Real.sqrt (ρ₀ x)) = fun _ : Euc d => (0 : ℝ) := by
    funext x; simp
  refine ⟨one_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T'
    have := HRS.MS.S21.s21_mf_stationary hd hs0 hsd hq hβ hρ T'
    rw [HRS.MS.S21.s21_dyn_eq]
    exact this
  · funext x; simp [perturbedDensity]
  · intro t _ x; exact ⟨by simp, by simp⟩
  · intro t _
    show MemOsc _ (fun x => (ρ₀ x - ρ₀ x) / Real.sqrt (ρ₀ x)) ∧
      oscNorm _ (fun x => (ρ₀ x - ρ₀ x) / Real.sqrt (ρ₀ x)) ≤ _
    rw [hzero]
    refine ⟨s611_memOsc_zero _, ?_⟩
    rw [s611_oscNorm_zero]
    positivity
  · intro t _
    have e1 : (fun y => Real.log (ρ₀ y / ρ₀ y)) = fun _ : Euc d => (0 : ℝ) := by
      funext y
      by_cases h : ρ₀ y = 0
      · simp [h]
      · simp [h]
    have e2 : (fun x => β⁻¹ • gradient (fun y => Real.log (ρ₀ y)) x + q • x +
        convGradConvW (rieszKernelGrad d s) ρ₀ x) = fun _ : Euc d => (0 : Euc d) := by
      funext x
      exact HRS.MS.Mov0.mv0_thermal_force hd hs0 hsd hq hβ hρ x
    have e3 : (fun x => gradient (fun y => Real.log (ρ₀ y / ρ₀ y)) x) = fun _ : Euc d => (0 : Euc d) := by
      rw [e1]; funext x; simp [gradient]
    show cbNormVecE _ (fun x => gradient (fun y => Real.log (ρ₀ y / ρ₀ y)) x) +
      cbNormVecE _ (fun x => β⁻¹ • gradient (fun y => Real.log (ρ₀ y)) x + q • x +
        convGradConvW (rieszKernelGrad d s) ρ₀ x) ≤ _
    rw [e2, e3, movtr_cbNormVecE_const]
    simp
  · exact continuousOn_const
  · intro t _
    exact (HRS.MS.Mov0.mv0_hgauss hd hs0 hsd hq hβ hρ).1.continuous

theorem s611_exists_admissible (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {q β : ℝ} (hq : 0 < q)
    (hβ : 0 < β) {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) (εstar : ℝ) (hε : 0 < εstar) :
    ∃ ψ : Euc d → ℝ, IsAdmissiblePerturbation ρ₀ εstar 0 ψ := by
  obtain ⟨M₀, c, S, hc, hTc⟩ := s611_tcref_of_thermal hd hs0 hsd hq hβ hρ
  have hρc : Continuous ρ₀ := hTc.smooth.continuous
  let i0 : Fin d := ⟨0, by omega⟩
  let x2 : Euc d := (5 : ℝ) • (EuclideanSpace.single i0 (1 : ℝ))
  let b1 : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  let b2 : ContDiffBump x2 := ⟨1, 2, one_pos, one_lt_two⟩
  have hI : ∀ {x0 : Euc d} (b : ContDiffBump x0), 0 < ∫ x, b x * ρ₀ x := by
    intro x0 b
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0)
      (b.continuous.mul hρc) (b.hasCompactSupport.mul_right)
      (fun x => mul_nonneg b.nonneg (hTc.pos x).le) ?_
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact (mul_pos one_pos (hTc.pos x0)).ne'
  have hint : ∀ {x0 : Euc d} (b : ContDiffBump x0), Integrable (fun x => b x * ρ₀ x) := fun b =>
    (b.continuous.mul hρc).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  set I1 := ∫ x, b1 x * ρ₀ x with hI1
  set I2 := ∫ x, b2 x * ρ₀ x with hI2
  have hI2pos : 0 < I2 := hI b2
  refine ⟨fun x => b1 x - (I1 / I2) * b2 x, ?_, ?_, ?_, ?_, ?_⟩
  · exact b1.contDiff.sub (contDiff_const.mul b2.contDiff)
  · exact b1.hasCompactSupport.sub (b2.hasCompactSupport.mul_left)
  · intro h
    have h0 := congrFun h 0
    have hb2 : b2 0 = 0 := by
      refine Function.notMem_support.1 ?_
      rw [b2.support_eq]
      intro hmem
      have : dist (0 : Euc d) x2 < 2 := hmem
      have hx2 : ‖x2‖ = 5 := by
        simp only [x2, norm_smul, Real.norm_eq_abs]
        have : ‖(EuclideanSpace.single i0 (1 : ℝ) : Euc d)‖ = 1 := by simp
        rw [this]; norm_num
      rw [dist_eq_norm, zero_sub, norm_neg, hx2] at this
      norm_num at this
    have hb1 : b1 0 = 1 := b1.one_of_mem_closedBall (Metric.mem_closedBall_self b1.rIn_pos.le)
    simp only [Pi.zero_apply, hb2, hb1] at h0
    norm_num at h0
  · have e : (fun x => (b1 x - (I1 / I2) * b2 x) * ρ₀ x) =
        fun x => b1 x * ρ₀ x - (I1 / I2) * (b2 x * ρ₀ x) := by funext x; ring
    rw [e, integral_sub (hint b1) ((hint b2).const_mul _), integral_const_mul]
    show I1 - I1 / I2 * I2 = 0
    field_simp
    ring
  · have e1 : (fun x : Euc d => (0 : ℝ) * (b1 x - (I1 / I2) * b2 x)) = fun _ => 0 := by funext x; simp
    have e2 : (fun x : Euc d => (0 : ℝ) * Real.sqrt (ρ₀ x) * (b1 x - (I1 / I2) * b2 x)) = fun _ => 0 := by
      funext x; simp
    rw [e1, e2, s611_oscNorm_zero]
    simp [HRS.cbNorm, hε.le]

end HRS.MS.TransOp

end
