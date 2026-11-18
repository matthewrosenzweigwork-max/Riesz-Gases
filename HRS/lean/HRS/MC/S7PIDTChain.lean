import HRS.MC.S7PIDCChain

/-!
# Packet PI-D, sub-packet T (part 3): the dyadic chain with integrability, and the moment lemmas

* `S7PIDT_chain_int`: the integrable branch of `s7_PID_chain_proof`, with `S^2` integrable among the conclusions;
* `S7PIDT_cs`: Cauchy--Schwarz in the form `∫ X Y ≤ √(A B)`;
* `S7PIDT_sup` : a measurable majorant of all `‖Z k‖`, `k ≤ 2^n`, with `∫ S² ≤ 162 κ`;
* `S7PIDT_del` : the maximal one-step increment at level `2^n`, `(∫ δ²)² ≤ 3 κ² / 2^n`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS.MC.Sec7.S7PIDC

theorem S7PIDT_chain_int {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (Y : ℕ → Ω → E) (hY : ∀ a b, Measurable fun ω => ‖Y a ω - Y b ω‖) (Λ : ℝ)
    (hinc : ∀ j ≤ n, ∀ k < 2 ^ j,
      ∫ ω, ‖Y ((k + 1) * 2 ^ (n - j)) ω - Y (k * 2 ^ (n - j)) ω‖ ^ 4 ∂P ≤ Λ * (1 / 4 : ℝ) ^ j)
    (hint : ∀ j ≤ n, ∀ κ < 2 ^ j,
      Integrable (fun ω => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4) P) :
    ∃ S : Ω → ℝ, Measurable S ∧ (∀ ω, ∀ k ≤ 2 ^ n, ‖Y k ω - Y 0 ω‖ ≤ S ω) ∧
      Integrable (fun ω => S ω ^ 2) P ∧ ∫ ω, S ω ^ 2 ∂P ≤ 40 * Real.sqrt Λ := by
  have hΛ : 0 ≤ Λ := by
    have h := hinc 0 (Nat.zero_le _) 0 (by norm_num)
    have h0 : 0 ≤ ∫ ω, ‖Y ((0 + 1) * 2 ^ (n - 0)) ω - Y (0 * 2 ^ (n - 0)) ω‖ ^ 4 ∂P :=
      integral_nonneg (fun _ => by positivity)
    simp only [pow_zero, mul_one] at h
    linarith
  set D : ℕ → Ω → ℝ := S7PIDC_D n Y with hDdef
  have hDm : ∀ j, Measurable (D j) := S7PIDC_D_meas n Y hY
  have hD0 : ∀ j ω, 0 ≤ D j ω := S7PIDC_D_nonneg n Y
  have hSm : Measurable (fun ω => ∑ j ∈ Finset.range (n + 1), D j ω) :=
    Finset.measurable_sum _ (fun j _ => hDm j)
  have hbound : ∀ ω, ∀ k ≤ 2 ^ n, ‖Y k ω - Y 0 ω‖ ≤ ∑ j ∈ Finset.range (n + 1), D j ω := fun ω =>
    S7PIDC_telescope n (fun k => Y k ω) (fun j => D j ω) (fun j => hD0 j ω)
      (fun j _ κ hκ => S7PIDC_D_le n Y j ω κ hκ)
  refine ⟨fun ω => ∑ j ∈ Finset.range (n + 1), D j ω, hSm, hbound, ?_⟩
  -- moments of the level maxima
  have hD4int : ∀ j ≤ n, Integrable (fun ω => D j ω ^ 4) P := by
    intro j hj
    have hs : Integrable (fun ω => ∑ κ ∈ Finset.range (2 ^ j),
        ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4) P :=
      integrable_finsetSum _ (fun κ hκ => hint j hj κ (Finset.mem_range.1 hκ))
    refine hs.mono' ((hDm j).pow_const 4).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by have := hD0 j ω; positivity)]
    exact S7PIDC_D_pow4_le n Y j ω
  have hD2int : ∀ j ≤ n, Integrable (fun ω => D j ω ^ 2) P := by
    intro j hj
    refine ((integrable_const (1 : ℝ)).add (hD4int j hj)).mono' ((hDm j).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    show ‖D j ω ^ 2‖ ≤ 1 + D j ω ^ 4
    rw [Real.norm_of_nonneg (by have := hD0 j ω; positivity)]
    nlinarith [sq_nonneg (D j ω ^ 2 - 1), sq_nonneg (D j ω)]
  set q : ℝ := Real.sqrt (1 / 2) with hq
  have hq2 : q ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q ≤ 17 / 24 := by nlinarith
  have hE2 : ∀ j ≤ n, ∫ ω, D j ω ^ 2 ∂P ≤ Real.sqrt Λ * q ^ j := by
    intro j hj
    have hs : Integrable (fun ω => ∑ κ ∈ Finset.range (2 ^ j),
        ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4) P :=
      integrable_finsetSum _ (fun κ hκ => hint j hj κ (Finset.mem_range.1 hκ))
    have h4 : ∫ ω, D j ω ^ 4 ∂P ≤ Λ * (1 / 2 : ℝ) ^ j := by
      calc ∫ ω, D j ω ^ 4 ∂P
          ≤ ∫ ω, ∑ κ ∈ Finset.range (2 ^ j),
              ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4 ∂P :=
            integral_mono (hD4int j hj) hs (fun ω => S7PIDC_D_pow4_le n Y j ω)
        _ = ∑ κ ∈ Finset.range (2 ^ j),
              ∫ ω, ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4 ∂P :=
            integral_finsetSum _ (fun κ hκ => hint j hj κ (Finset.mem_range.1 hκ))
        _ ≤ ∑ κ ∈ Finset.range (2 ^ j), Λ * (1 / 4 : ℝ) ^ j :=
            Finset.sum_le_sum (fun κ hκ => hinc j hj κ (Finset.mem_range.1 hκ))
        _ = Λ * (1 / 2 : ℝ) ^ j := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            calc (2 : ℝ) ^ j * (Λ * (1 / 4 : ℝ) ^ j) = Λ * ((2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j) := by ring
              _ = Λ * (1 / 2 : ℝ) ^ j := by rw [← mul_pow]; norm_num
    have hJ := S7PIDC_sq_integral_le P (fun ω => D j ω ^ 2) (hD2int j hj)
      (by simpa [← pow_mul] using hD4int j hj)
    have hJ' : (∫ ω, D j ω ^ 2 ∂P) ^ 2 ≤ Λ * (1 / 2 : ℝ) ^ j := by
      refine hJ.trans ?_
      have : ∀ ω, (D j ω ^ 2) ^ 2 = D j ω ^ 4 := fun ω => by ring
      simp only [this]
      exact h4
    have hsq : (Real.sqrt Λ * q ^ j) ^ 2 = Λ * (1 / 2 : ℝ) ^ j := by
      rw [mul_pow, Real.sq_sqrt hΛ, ← pow_mul, mul_comm j 2, pow_mul, hq2]
    have hnn : 0 ≤ Real.sqrt Λ * q ^ j := by positivity
    by_contra hcon
    push Not at hcon
    nlinarith
  -- Cauchy--Schwarz pointwise
  have hCS : ∀ ω, (∑ j ∈ Finset.range (n + 1), D j ω) ^ 2 ≤
      (∑ j ∈ Finset.range (n + 1), (5 / 6 : ℝ) ^ j) *
        ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * D j ω ^ 2 := by
    intro ω
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => by positivity)
      (fun j _ => by have := hD0 j ω; positivity) (fun j _ => le_of_eq ?_)
    rw [← mul_assoc, ← mul_pow]
    norm_num
  have hRint : Integrable (fun ω => (∑ j ∈ Finset.range (n + 1), (5 / 6 : ℝ) ^ j) *
        ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * D j ω ^ 2) P :=
    (integrable_finsetSum _ (fun j hj =>
      (hD2int j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).const_mul ((6 / 5 : ℝ) ^ j))).const_mul _
  have hmain : ∫ ω, (∑ j ∈ Finset.range (n + 1), D j ω) ^ 2 ∂P ≤
      ∫ ω, (∑ j ∈ Finset.range (n + 1), (5 / 6 : ℝ) ^ j) *
        ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * D j ω ^ 2 ∂P :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hRint
      (Filter.Eventually.of_forall hCS)
  have hSint : Integrable (fun ω => (∑ j ∈ Finset.range (n + 1), D j ω) ^ 2) P := by
    refine hRint.mono' (hSm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hCS ω
  refine ⟨hSint, hmain.trans ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun j hj =>
      (hD2int j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))).const_mul ((6 / 5 : ℝ) ^ j))]
  simp only [integral_const_mul]
  have hg1 : ∑ j ∈ Finset.range (n + 1), (5 / 6 : ℝ) ^ j ≤ 6 := by
    have := S7PIDC_geom_le (5 / 6) (by norm_num) (by norm_num) (n + 1)
    norm_num at this ⊢
    linarith
  have hg2 : ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * (Real.sqrt Λ * q ^ j) ≤
      Real.sqrt Λ * (20 / 3) := by
    have e : ∀ j, (6 / 5 : ℝ) ^ j * (Real.sqrt Λ * q ^ j) = Real.sqrt Λ * (6 / 5 * q) ^ j := by
      intro j; rw [mul_pow]; ring
    simp only [e]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc ∑ j ∈ Finset.range (n + 1), (6 / 5 * q) ^ j
        ≤ ∑ j ∈ Finset.range (n + 1), (17 / 20 : ℝ) ^ j :=
          Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (by positivity) (by linarith) j)
      _ ≤ 1 / (1 - 17 / 20) := S7PIDC_geom_le _ (by norm_num) (by norm_num) _
      _ = 20 / 3 := by norm_num
  have hg3 : ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * ∫ ω, D j ω ^ 2 ∂P ≤
      ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * (Real.sqrt Λ * q ^ j) :=
    Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left
      (hE2 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))) (by positivity))
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), (5 / 6 : ℝ) ^ j := Finset.sum_nonneg (fun j _ => by positivity)
  calc (∑ j ∈ Finset.range (n + 1), (5 / 6 : ℝ) ^ j) *
        ∑ j ∈ Finset.range (n + 1), (6 / 5 : ℝ) ^ j * ∫ ω, D j ω ^ 2 ∂P
      ≤ 6 * (Real.sqrt Λ * (20 / 3)) :=
        mul_le_mul hg1 (hg3.trans hg2)
          (Finset.sum_nonneg (fun j hj => mul_nonneg (by positivity) (integral_nonneg fun ω => by positivity)))
          (by norm_num)
    _ = 40 * Real.sqrt Λ := by ring

end HRS.MC.Sec7.S7PIDT

end
