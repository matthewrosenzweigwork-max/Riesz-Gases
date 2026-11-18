import HRS.MP.SelfSimP4MolH4

/-!
# MPP4MOL stage 5c (18): growth of `b` and `V` from the hypotheses of the interface lemma
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_V_growth {V : EucConfig d N → ℝ} {c : EucConfig d N → EucConfig d N} {B K : ℝ} (hK : 0 ≤ K)
    (hV : ∀ x, HasFDerivAt V (-(p4InnerL (c x))) x) (hc : ∀ x, ‖c x‖ ≤ B + K * ‖x‖) (x : EucConfig d N) :
    |V x - V 0| ≤ N * (B + K * ‖x‖) * ‖x‖ := by
  have hconv : Convex ℝ (Metric.closedBall (0 : EucConfig d N) ‖x‖) := convex_closedBall _ _
  have hx0 : (0 : EucConfig d N) ∈ Metric.closedBall (0 : EucConfig d N) ‖x‖ := by
    simp
  have hxx : x ∈ Metric.closedBall (0 : EucConfig d N) ‖x‖ := by simp
  have := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := V) (f' := fun y => -(p4InnerL (c y)))
    (C := N * (B + K * ‖x‖)) (fun y _ => (hV y).hasFDerivWithinAt) (fun y hy => by
      rw [norm_neg]
      refine (p4m_innerL_norm_le (c y)).trans ?_
      have hy' : ‖y‖ ≤ ‖x‖ := by simpa using hy
      have := hc y
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc (N : ℝ) * ‖c y‖ ≤ N * (B + K * ‖x‖) := by
            gcongr
            nlinarith [mul_le_mul_of_nonneg_left hy' hK]) hx0 hxx
  rw [Real.norm_eq_abs] at this
  simpa [mul_assoc] using this

theorem p4m_b_growth {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} {K : ℝ≥0}
    (hbc : Continuous (Function.uncurry b)) (hlip : ∀ τ ∈ Set.Icc (0 : ℝ) T, LipschitzWith K (b τ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖b τ y‖ ≤ B + K * ‖y‖ := by
  have hc : Continuous (fun τ : ℝ => b τ 0) :=
    hbc.comp (Continuous.prodMk continuous_id continuous_const)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun τ : ℝ => b τ 0)
    (s := Set.Icc (0 : ℝ) T) hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun τ hτ y => ?_⟩
  have h1 := hC τ hτ
  have h2 := (hlip τ hτ).dist_le_mul y 0
  rw [dist_eq_norm, dist_zero_right] at h2
  calc ‖b τ y‖ = ‖b τ 0 + (b τ y - b τ 0)‖ := by congr 1; abel
    _ ≤ ‖b τ 0‖ + ‖b τ y - b τ 0‖ := norm_add_le _ _
    _ ≤ max C 0 + K * ‖y‖ := add_le_add (h1.trans (le_max_left _ _)) h2

theorem p4m_V_bound {V : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} {K : ℝ≥0}
    (hVc : Continuous (Function.uncurry V)) (hbc : Continuous (Function.uncurry b))
    (hgrad : ∀ τ x, HasFDerivAt (V τ) (-(p4InnerL (b τ x))) x)
    (hlip : ∀ τ ∈ Set.Icc (0 : ℝ) T, LipschitzWith K (b τ)) :
    ∃ CV : ℝ, 0 ≤ CV ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ x, |V τ x| ≤ CV * (1 + p4m_q x) := by
  obtain ⟨B, hB, hbg⟩ := p4m_b_growth hbc hlip
  have hc : Continuous (fun τ : ℝ => V τ 0) :=
    hVc.comp (Continuous.prodMk continuous_id continuous_const)
  obtain ⟨V0, hV0⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := fun τ : ℝ => V τ 0)
    (s := Set.Icc (0 : ℝ) T) hc.continuousOn
  have hK : (0 : ℝ) ≤ K := K.2
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  refine ⟨max V0 0 + N * B + N * K, by positivity, fun τ hτ x => ?_⟩
  have h1 := p4m_V_growth hK (hgrad τ) (fun y => hbg τ hτ y) x
  have h2 := hV0 τ hτ
  rw [Real.norm_eq_abs] at h2
  have hq := p4m_norm_sq_le_q x
  have hn0 := norm_nonneg x
  have hn1 : ‖x‖ ≤ 1 + p4m_q x := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hq0 : 0 ≤ p4m_q x := p4m_q_nonneg x
  have hm0 : 0 ≤ max V0 0 := le_max_right _ _
  have hV0' : |V τ 0| ≤ max V0 0 := h2.trans (le_max_left _ _)
  have h3 : |V τ x| ≤ |V τ 0| + |V τ x - V τ 0| := by
    calc |V τ x| = |V τ 0 + (V τ x - V τ 0)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have h4 : (N : ℝ) * (B + K * ‖x‖) * ‖x‖ ≤ N * B * (1 + p4m_q x) + N * K * p4m_q x := by
    have e : (N : ℝ) * (B + K * ‖x‖) * ‖x‖ = N * B * ‖x‖ + N * K * ‖x‖ ^ 2 := by ring
    rw [e]
    have a1 : (N : ℝ) * B * ‖x‖ ≤ N * B * (1 + p4m_q x) := mul_le_mul_of_nonneg_left hn1 (by positivity)
    have a2 : (N : ℝ) * K * ‖x‖ ^ 2 ≤ N * K * p4m_q x := mul_le_mul_of_nonneg_left hq (by positivity)
    linarith
  nlinarith [mul_nonneg hN (mul_nonneg hK hq0), mul_nonneg hm0 hq0]

end HRS.MP.SelfSimP4Mol
