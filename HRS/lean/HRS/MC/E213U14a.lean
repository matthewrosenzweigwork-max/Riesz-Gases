import HRS.MC.E213U11i
import HRS.MC.E213U12a

/-!
# Packet e213u14 (part a): geometric weights and the expectation of a block-sum bound

* `u14_geom`: `∑_{k < ⌈max (a-Rw) 0⌉} e^{-c(a-(k+1))} ≤ e^{2c}/(e^c-1) · e^{-c Rw}`.
* `u14_expect_bound`: if `|g| ≤ K ∑_k w_k Y_k` a.s. with integrable `Y_k`, `E Y_k ≤ M`, then `|E g| ≤ K · A · M · e^{-c Rw}`.
Namespace `HRS.MC.E213U14`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U14

theorem u14_geom {c a Rw : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hRw : 0 ≤ Rw) :
    ∑ k ∈ Finset.range ⌈max (a - Rw) 0⌉₊, Real.exp (-c * (a - ((k : ℝ) + 1))) ≤
      Real.exp (2 * c) / (Real.exp c - 1) * Real.exp (-c * Rw) := by
  have hn0 : 1 < Real.exp c := by have := Real.add_one_lt_exp hc.ne'; linarith
  have hpos : 0 < Real.exp c - 1 := by linarith
  rcases Nat.eq_zero_or_pos ⌈max (a - Rw) 0⌉₊ with h0 | h0
  · rw [h0]
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · have hb : 0 < max (a - Rw) 0 := Nat.ceil_pos.1 h0
    have hb' : max (a - Rw) 0 = a - Rw := by
      rcases max_cases (a - Rw) 0 with h | h
      · exact h.1
      · exfalso; linarith [h.1, h.2]
    have hn : (⌈max (a - Rw) 0⌉₊ : ℝ) < a - Rw + 1 := by
      have := Nat.ceil_lt_add_one hb.le
      rw [hb'] at this ⊢
      exact this
    have hterm : ∀ k : ℕ, Real.exp (-c * (a - ((k : ℝ) + 1))) = Real.exp (c * (1 - a)) * Real.exp c ^ k := by
      intro k
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, geom_sum_eq hn0.ne']
    have h1 : Real.exp c ^ ⌈max (a - Rw) 0⌉₊ ≤ Real.exp (c * (a - Rw + 1)) := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (c * (1 - a)) * ((Real.exp c ^ ⌈max (a - Rw) 0⌉₊ - 1) / (Real.exp c - 1))
        ≤ Real.exp (c * (1 - a)) * (Real.exp (c * (a - Rw + 1)) / (Real.exp c - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact div_le_div_of_nonneg_right (by linarith) hpos.le
      _ = Real.exp (2 * c) / (Real.exp c - 1) * Real.exp (-c * Rw) := by
          rw [← mul_div_assoc, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
          congr 2; ring

theorem u14_expect_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : Ω → ℝ) (Y : ℕ → Ω → ℝ) (hY0 : ∀ k ω, 0 ≤ Y k ω) (hYi : ∀ k, Integrable (Y k) P)
    (M : ℝ) (hYM : ∀ k, ∫ ω, Y k ω ∂P ≤ M) {c a Rw K : ℝ} (hc : 0 < c) (ha : 0 ≤ a) (hRw : 0 ≤ Rw) (hK : 0 ≤ K)
    (hpt : ∀ᵐ ω ∂P, |G ω| ≤ K * ∑ k ∈ Finset.range ⌈max (a - Rw) 0⌉₊,
      Real.exp (-c * (a - ((k : ℝ) + 1))) * Y k ω) :
    |∫ ω, G ω ∂P| ≤ K * (Real.exp (2 * c) / (Real.exp c - 1) * M) * Real.exp (-c * Rw) := by
  set n := ⌈max (a - Rw) 0⌉₊ with hn
  have hI : Integrable (fun ω => K * ∑ k ∈ Finset.range n, Real.exp (-c * (a - ((k : ℝ) + 1))) * Y k ω) P :=
    (integrable_finsetSum _ fun k _ => (hYi k).const_mul _).const_mul _
  have h1 := norm_integral_le_of_norm_le hI (by
    filter_upwards [hpt] with ω h
    rwa [Real.norm_eq_abs])
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun k _ => (hYi k).const_mul _]
  have hM0 : 0 ≤ M := le_trans (integral_nonneg (hY0 0)) (hYM 0)
  have h2 : ∑ k ∈ Finset.range n, ∫ ω, Real.exp (-c * (a - ((k : ℝ) + 1))) * Y k ω ∂P ≤
      (∑ k ∈ Finset.range n, Real.exp (-c * (a - ((k : ℝ) + 1)))) * M := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hYM k) (Real.exp_pos _).le
  have h3 := u14_geom (c := c) (a := a) (Rw := Rw) hc ha hRw
  calc K * ∑ k ∈ Finset.range n, ∫ ω, Real.exp (-c * (a - ((k : ℝ) + 1))) * Y k ω ∂P
      ≤ K * ((∑ k ∈ Finset.range n, Real.exp (-c * (a - ((k : ℝ) + 1)))) * M) :=
        mul_le_mul_of_nonneg_left h2 hK
    _ ≤ K * ((Real.exp (2 * c) / (Real.exp c - 1) * Real.exp (-c * Rw)) * M) := by
        gcongr
    _ = _ := by ring

end HRS.MC.E213U14

end
