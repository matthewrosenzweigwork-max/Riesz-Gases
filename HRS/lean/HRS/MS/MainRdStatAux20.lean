import HRS.MS.MainRdStatAux19

/-!
# SA2, packet 10a: arithmetic and complex-test bookkeeping for the final assembly
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-- `K Y r ≤ statBound C 1 t X r` for `Y ≤ M X (1+X)`, `K M ≤ C`. -/
theorem sa2_stat_arith {K Y M X r C t : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hX : 0 ≤ X) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hY : Y ≤ M * (X * (1 + X))) (hC : K * M ≤ C) :
    K * Y * r ≤ HRS.Main.statBound C 1 t X r := by
  unfold HRS.Main.statBound
  have hC0 : 0 ≤ C := (mul_nonneg hK hM).trans hC
  have hex : 1 ≤ Real.exp (1 * t) := by
    rw [one_mul]; exact Real.one_le_exp ht
  have hXX : 0 ≤ X * (1 + X) := by positivity
  calc K * Y * r ≤ K * (M * (X * (1 + X))) * r := by gcongr
    _ = (K * M) * (X * (1 + X)) * r := by ring
    _ ≤ C * (X * (1 + X)) * r := by gcongr
    _ ≤ C * Real.exp (1 * t) * (X * (1 + X)) * r := by
        have : C * (X * (1 + X)) ≤ C * Real.exp (1 * t) * (X * (1 + X)) := by
          have := mul_le_mul_of_nonneg_left hex hC0
          nlinarith [mul_nonneg hC0 hXX]
        exact mul_le_mul_of_nonneg_right this hr
    _ = C * Real.exp (1 * t) * X * (1 + X) * r := by ring

theorem sa2_Bs_bound {Kp κ X : ℝ} (hKp : 0 ≤ Kp) (hκ : Kp ≤ κ) (hX : 0 ≤ X) :
    Kp * X + (Kp * X) ^ 2 ≤ (κ + κ ^ 2) * (X * (1 + X)) := by
  have h1 : Kp * X ≤ κ * X := mul_le_mul_of_nonneg_right hκ hX
  have h0 : 0 ≤ Kp * X := mul_nonneg hKp hX
  have h2 : (Kp * X) ^ 2 ≤ (κ * X) ^ 2 := pow_le_pow_left₀ h0 h1 2
  nlinarith [sq_nonneg X, mul_nonneg hX hX]

theorem sa2_Bs_bound1 {Kp κ X : ℝ} (hKp : 0 ≤ Kp) (hκ : Kp ≤ κ) (hX : 0 ≤ X) :
    Kp * X ≤ (κ + κ ^ 2) * (X * (1 + X)) := by
  have := sa2_Bs_bound hKp hκ hX
  nlinarith [sq_nonneg (Kp * X)]

theorem sa2_Bs_final {Bs κ X : ℝ} (hBs0 : 0 ≤ Bs) (hBs : Bs ≤ κ * X) (hκ : 0 ≤ κ) (hX : 0 ≤ X) :
    Bs + Bs ^ 2 ≤ (κ + κ ^ 2) * (X * (1 + X)) := by
  have h2 : Bs ^ 2 ≤ (κ * X) ^ 2 := pow_le_pow_left₀ hBs0 hBs 2
  have := sa2_Bs_bound hκ le_rfl hX
  linarith

/-- real and imaginary parts of admissible complex tests are admissible -/
theorem sa2_realIm_mem {χ : Euc d → ℝ} {n : ℕ} {φ : Fin (n + 1) → Euc d → ℂ}
    (h : ∀ a, (ulocClass (mStar d) χ).memC (φ a)) (ab : Fin (n + 1) × Bool) :
    (ulocClass (mStar d) χ).mem (realImPartsRd φ ab) := by
  obtain ⟨a, b⟩ := ab
  cases b
  · exact (h a).1
  · exact (h a).2

/-- the sum of the norms of the real and imaginary parts is dominated by twice the complex norms -/
theorem sa2_realIm_X {χ : Euc d → ℝ} {n : ℕ} (φ : Fin (n + 1) → Euc d → ℂ) :
    sa2X χ (realImPartsRd φ) ≤ 2 * ∑ a, (ulocClass (mStar d) χ).normC (φ a) := by
  unfold sa2X
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Fintype.sum_bool]
  have hre : realImPartsRd φ (a, false) = fun x => (φ a x).re := by
    funext x; simp [realImPartsRd]
  have him : realImPartsRd φ (a, true) = fun x => (φ a x).im := by
    funext x; simp [realImPartsRd]
  rw [hre, him]
  unfold TestClassRd.normC ulocClass
  simp only
  set u := (ulocNormE (mStar d) χ fun x => (φ a x).re).toReal with hu
  set v := (ulocNormE (mStar d) χ fun x => (φ a x).im).toReal with hv
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have h1 : u ≤ Real.sqrt (u ^ 2 + v ^ 2) := by
    calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v])
  have h2 : v ≤ Real.sqrt (u ^ 2 + v ^ 2) := by
    calc v = Real.sqrt (v ^ 2) := (Real.sqrt_sq hv0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  linarith

end HRS.MS.MainRdStat
