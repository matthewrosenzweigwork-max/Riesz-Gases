import HRS.MS.R26T8AD01

/-!
# S8.2 T8A O01a: `PairCorrector` is monotone in the amplitude
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_o01_pairWeight_nonneg {d : ℕ} (M : ℝ) (x y : Euc d) : 0 ≤ Phase2S82.pairWeight M x y := by
  unfold Phase2S82.pairWeight jbracket
  exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

theorem r26t8a_o01_PairCorrector_mono {d : ℕ} {a beta M A A' : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (h : PairCorrector a beta rho M A f Q) (hA : A ≤ A') :
    PairCorrector a beta rho M A' f Q where
  measurable := h.measurable
  smooth := h.smooth
  symmetric := h.symmetric
  canonical := h.canonical
  poisson := h.poisson
  value := by
    intro x y hxy
    refine (h.value x y hxy).trans ?_
    have h1 := r26t8a_o01_pairWeight_nonneg (d := d) M x y
    have h2 : 0 ≤ 1 + smallRadius x y ^ (2 - criticalS d) +
        (if d = 4 then |Real.log (smallRadius x y)| else 0) := by
      have : 0 ≤ smallRadius x y := le_min zero_le_one (norm_nonneg _)
      have := Real.rpow_nonneg this (2 - criticalS d)
      split_ifs <;> positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h1) h2
  gradient := by
    intro x y hxy
    refine (h.gradient x y hxy).trans ?_
    have h1 := r26t8a_o01_pairWeight_nonneg (d := d) M x y
    have h2 : 0 ≤ 1 + smallRadius x y ^ (1 - criticalS d) := by
      have : 0 ≤ smallRadius x y := le_min zero_le_one (norm_nonneg _)
      have := Real.rpow_nonneg this (1 - criticalS d)
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h1) h2
  hessian := by
    intro x y hxy
    refine (h.hessian x y hxy).trans ?_
    have h1 := r26t8a_o01_pairWeight_nonneg (d := d) M x y
    have h2 : 0 ≤ 1 + smallRadius x y ^ (-criticalS d) := by
      have : 0 ≤ smallRadius x y := le_min zero_le_one (norm_nonneg _)
      have := Real.rpow_nonneg this (-criticalS d)
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h1) h2
  tangential := by
    obtain ⟨hs, hb⟩ := h.tangential
    refine ⟨hs, fun p q hpq X z hz => (hb p q hpq X z hz).trans ?_⟩
    have h1 := r26t8a_o01_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
    have h2 : 0 ≤ 1 + (min 1 ‖z‖) ^ (-(criticalS d - 2 + q)) * (1 + |Real.log (min 1 ‖z‖)|) ^ 1 := by
      have : 0 ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
      have h3 := Real.rpow_nonneg this (-(criticalS d - 2 + q))
      have h4 : 0 ≤ (1 + |Real.log (min 1 ‖z‖)|) ^ 1 := by positivity
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h1) h2
  nonlocal := by
    obtain ⟨hc, hb⟩ := h.nonlocal
    refine ⟨hc, fun x y hxy => (hb x y hxy).trans ?_⟩
    have h1 := r26t8a_o01_pairWeight_nonneg (d := d) M x y
    have h2 : 0 ≤ 1 + smallRadius x y ^ (-criticalS d) := by
      have : 0 ≤ smallRadius x y := le_min zero_le_one (norm_nonneg _)
      have := Real.rpow_nonneg this (-criticalS d)
      positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA h1) h2

end HRS.MS.R26T8A

end
