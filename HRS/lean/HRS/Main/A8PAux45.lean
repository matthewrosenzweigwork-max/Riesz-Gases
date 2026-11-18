import HRS.Main.A8PAux44

/-!
# Packet A8P, part 45: real-number lemmas for the final assembly
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_masterRate_nonneg {ε q σ 𝔈 E : ℝ} {N : ℕ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (hσ : 0 ≤ σ)
    (h𝔈 : 0 ≤ 𝔈) (hE : 0 ≤ E) : 0 ≤ masterRate d ε q σ 𝔈 E N := by
  unfold masterRate
  have h1 : 0 ≤ 𝔈 ^ ((1 : ℝ) / 4) := Real.rpow_nonneg h𝔈 _
  have h2 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / (2 * d)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have := Real.sqrt_nonneg q
  positivity

theorem a8p_stat_real {Cw C Λ₁ t X K c0 r : ℝ} (hCw0 : 0 ≤ Cw) (hr : 0 ≤ r) (hK : 0 ≤ K)
    (hKb : K ≤ c0 * Real.exp (|Λ₁| * t) * X) (hc00 : 0 ≤ c0) (hc0 : c0 ≤ 2) (hX : 0 ≤ X)
    (ht : 0 ≤ t) (hC : 4 * Cw ≤ C) :
    Cw * (K + K ^ 2) * r ≤ statBound C (2 * |Λ₁| + 1) t X r := by
  have h := a8p_K_arith hK hKb hc00 hc0 hX ht
  unfold statBound
  have hE : 0 ≤ Real.exp ((2 * |Λ₁| + 1) * t) := (Real.exp_pos _).le
  have hEX : 0 ≤ Real.exp ((2 * |Λ₁| + 1) * t) * X * (1 + X) := by positivity
  calc Cw * (K + K ^ 2) * r ≤ Cw * (4 * Real.exp ((2 * |Λ₁| + 1) * t) * X * (1 + X)) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hCw0) hr
    _ = (4 * Cw) * (Real.exp ((2 * |Λ₁| + 1) * t) * X * (1 + X)) * r := by ring
    _ ≤ C * (Real.exp ((2 * |Λ₁| + 1) * t) * X * (1 + X)) * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hEX) hr
    _ = _ := by ring

end HRS.Main.A8P
