import HRS.MC.S7PIDTChain

/-!
# Packet PI-D, sub-packet T (part 4): moment lemmas (Cauchy--Schwarz, sup of a dyadic family, maximal increment)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS.MC.Sec7.S7PIDC

/-- Cauchy--Schwarz: `(∫ X Y)² ≤ A B` when `∫ X² ≤ A`, `∫ Y² ≤ B`. -/
theorem S7PIDT_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX2 : Integrable (fun ω => X ω ^ 2) P) (hY2 : Integrable (fun ω => Y ω ^ 2) P) {A B : ℝ}
    (hA : ∫ ω, X ω ^ 2 ∂P ≤ A) (hB : ∫ ω, Y ω ^ 2 ∂P ≤ B) :
    Integrable (fun ω => X ω * Y ω) P ∧ (∫ ω, X ω * Y ω ∂P) ^ 2 ≤ A * B := by
  have hXY : Integrable (fun ω => X ω * Y ω) P := by
    refine ((hX2.add hY2).const_mul (1 / 2)).mono' (hX.mul hY).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (X ω + Y ω), sq_nonneg (X ω - Y ω)]
  refine ⟨hXY, ?_⟩
  set a := ∫ ω, X ω ^ 2 ∂P with ha
  set b := ∫ ω, Y ω ^ 2 ∂P with hb
  set c := ∫ ω, X ω * Y ω ∂P with hc
  have ha0 : 0 ≤ a := integral_nonneg fun ω => sq_nonneg _
  have hb0 : 0 ≤ b := integral_nonneg fun ω => sq_nonneg _
  have hdisc : ∀ t : ℝ, 0 ≤ a * (t * t) + (-2 * c) * t + b := by
    intro t
    have hexp : ∀ ω, (t * X ω - Y ω) ^ 2 = t ^ 2 * X ω ^ 2 - 2 * t * (X ω * Y ω) + Y ω ^ 2 := by
      intro ω; ring
    have hint : ∫ ω, (t * X ω - Y ω) ^ 2 ∂P = t ^ 2 * a - 2 * t * c + b := by
      simp_rw [hexp]
      rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
      · exact (hX2.const_mul _)
      · exact (hXY.const_mul _)
      · exact (hX2.const_mul _).sub (hXY.const_mul _)
      · exact hY2
    have hnn : 0 ≤ ∫ ω, (t * X ω - Y ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    nlinarith [hint, hnn]
  have hd := discrim_le_zero hdisc
  unfold discrim at hd
  have hab : a * b ≤ A * B := by
    have hA0 : 0 ≤ A := ha0.trans hA
    exact mul_le_mul hA hB hb0 hA0
  nlinarith [hd, hab]

/-- the dyadic variance bound at level `j` -/
lemma S7PIDT_dyadic_ratio (n j k : ℕ) (hj : j ≤ n) :
    ((((k + 1) * 2 ^ (n - j) : ℕ) : ℝ) - ((k * 2 ^ (n - j) : ℕ) : ℝ)) / (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ j := by
  have h1 : (2 : ℝ) ^ n = 2 ^ (n - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  have h2 : ((((k + 1) * 2 ^ (n - j) : ℕ) : ℝ) - ((k * 2 ^ (n - j) : ℕ) : ℝ)) = 2 ^ (n - j) := by
    push_cast; ring
  rw [h2, h1, one_div, inv_pow]
  field_simp

lemma S7PIDT_dyadic_le (n j k : ℕ) (hj : j ≤ n) (hk : k < 2 ^ j) : (k + 1) * 2 ^ (n - j) ≤ 2 ^ n := by
  calc (k + 1) * 2 ^ (n - j) ≤ 2 ^ j * 2 ^ (n - j) := Nat.mul_le_mul_right _ hk
    _ = 2 ^ n := by rw [← pow_add, Nat.add_sub_cancel' hj]

/-- a measurable majorant of the whole dyadic family -/
theorem S7PIDT_sup {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (Z : ℕ → Ω → E)
    (hZm : ∀ a b, Measurable fun ω => ‖Z a ω - Z b ω‖) (hZ0 : Measurable fun ω => ‖Z 0 ω‖)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (hI4 : ∀ a b, a ≤ 2 ^ n → b ≤ 2 ^ n → Integrable (fun ω => ‖Z a ω - Z b ω‖ ^ 4) P)
    (hv : ∀ a b : ℕ, a ≤ b → b ≤ 2 ^ n →
      ∫ ω, ‖Z b ω - Z a ω‖ ^ 4 ∂P ≤ 3 * (κ * (((b : ℝ) - a) / 2 ^ n)) ^ 2)
    (h0int : Integrable (fun ω => ‖Z 0 ω‖ ^ 2) P) (h0 : ∫ ω, ‖Z 0 ω‖ ^ 2 ∂P ≤ κ) :
    ∃ S : Ω → ℝ, Measurable S ∧ (∀ ω, 0 ≤ S ω) ∧ (∀ ω, ∀ k ≤ 2 ^ n, ‖Z k ω‖ ≤ S ω) ∧
      Integrable (fun ω => S ω ^ 2) P ∧ ∫ ω, S ω ^ 2 ∂P ≤ 162 * κ := by
  have hinc : ∀ j ≤ n, ∀ k < 2 ^ j,
      ∫ ω, ‖Z ((k + 1) * 2 ^ (n - j)) ω - Z (k * 2 ^ (n - j)) ω‖ ^ 4 ∂P ≤ (3 * κ ^ 2) * (1 / 4 : ℝ) ^ j := by
    intro j hj k hk
    have h := hv (k * 2 ^ (n - j)) ((k + 1) * 2 ^ (n - j)) (Nat.mul_le_mul_right _ (Nat.le_succ k))
      (S7PIDT_dyadic_le n j k hj hk)
    rw [S7PIDT_dyadic_ratio n j k hj] at h
    refine h.trans (le_of_eq ?_)
    have : ((1 / 2 : ℝ) ^ j) ^ 2 = (1 / 4 : ℝ) ^ j := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [mul_pow, this]; ring
  obtain ⟨Sc, hScm, hScb, hScint, hScle⟩ := S7PIDT_chain_int P n Z hZm (3 * κ ^ 2) hinc
    (fun j hj k hk => hI4 _ _ (S7PIDT_dyadic_le n j k hj hk)
      (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ k)) (S7PIDT_dyadic_le n j k hj hk)))
  have hsq : 40 * Real.sqrt (3 * κ ^ 2) ≤ 80 * κ := by
    have : Real.sqrt (3 * κ ^ 2) ≤ 2 * κ := by
      rw [Real.sqrt_le_iff]; constructor <;> nlinarith
    linarith
  have hSc0 : ∀ ω, 0 ≤ Sc ω := fun ω => by
    have := hScb ω 0 (Nat.zero_le _)
    simpa using this
  refine ⟨fun ω => ‖Z 0 ω‖ + Sc ω, hZ0.add hScm, fun ω => add_nonneg (norm_nonneg _) (hSc0 ω), ?_, ?_, ?_⟩
  · intro ω k hk
    have := hScb ω k hk
    have h2 : ‖Z k ω‖ ≤ ‖Z 0 ω‖ + ‖Z k ω - Z 0 ω‖ := by
      calc ‖Z k ω‖ = ‖Z 0 ω + (Z k ω - Z 0 ω)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  · have hb : Integrable (fun ω => 2 * ‖Z 0 ω‖ ^ 2 + 2 * Sc ω ^ 2) P :=
      (h0int.const_mul 2).add (hScint.const_mul 2)
    refine hb.mono' ((hZ0.add hScm).pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (‖Z 0 ω‖ - Sc ω)]
  · have hb : Integrable (fun ω => 2 * ‖Z 0 ω‖ ^ 2 + 2 * Sc ω ^ 2) P :=
      (h0int.const_mul 2).add (hScint.const_mul 2)
    have h1 : ∫ ω, (‖Z 0 ω‖ + Sc ω) ^ 2 ∂P ≤ ∫ ω, (2 * ‖Z 0 ω‖ ^ 2 + 2 * Sc ω ^ 2) ∂P :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hb
        (Filter.Eventually.of_forall fun ω => by nlinarith [sq_nonneg (‖Z 0 ω‖ - Sc ω)])
    rw [integral_add (h0int.const_mul 2) (hScint.const_mul 2), integral_const_mul, integral_const_mul] at h1
    linarith

/-- the maximal one-step increment at level `2^n` -/
theorem S7PIDT_del {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (Z : ℕ → Ω → E)
    (hZm : ∀ a b, Measurable fun ω => ‖Z a ω - Z b ω‖) (κ : ℝ)
    (hI4 : ∀ a b, a ≤ 2 ^ n → b ≤ 2 ^ n → Integrable (fun ω => ‖Z a ω - Z b ω‖ ^ 4) P)
    (hv : ∀ a b : ℕ, a ≤ b → b ≤ 2 ^ n →
      ∫ ω, ‖Z b ω - Z a ω‖ ^ 4 ∂P ≤ 3 * (κ * (((b : ℝ) - a) / 2 ^ n)) ^ 2) :
    ∃ δ : Ω → ℝ, Measurable δ ∧ (∀ ω, 0 ≤ δ ω) ∧ (∀ ω, ∀ k < 2 ^ n, ‖Z (k + 1) ω - Z k ω‖ ≤ δ ω) ∧
      Integrable (fun ω => δ ω ^ 2) P ∧ (∫ ω, δ ω ^ 2 ∂P) ^ 2 ≤ 3 * κ ^ 2 / 2 ^ n := by
  set δ : Ω → ℝ := S7PIDC_D n Z n with hδ
  have hδm : Measurable δ := S7PIDC_D_meas n Z hZm n
  have hδ0 : ∀ ω, 0 ≤ δ ω := S7PIDC_D_nonneg n Z n
  have hle : ∀ ω, ∀ k < 2 ^ n, ‖Z (k + 1) ω - Z k ω‖ ≤ δ ω := by
    intro ω k hk
    have := S7PIDC_D_le n Z n ω k hk
    simpa using this
  have hterm : ∀ κ' : ℕ, κ' < 2 ^ n →
      Integrable (fun ω => ‖Z ((κ' + 1) * 2 ^ (n - n)) ω - Z (κ' * 2 ^ (n - n)) ω‖ ^ 4) P := by
    intro k hk
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact hI4 _ _ (by omega) (by omega)
  have hs : Integrable (fun ω => ∑ κ' ∈ Finset.range (2 ^ n),
      ‖Z ((κ' + 1) * 2 ^ (n - n)) ω - Z (κ' * 2 ^ (n - n)) ω‖ ^ 4) P :=
    integrable_finsetSum _ (fun k hk => hterm k (Finset.mem_range.1 hk))
  have hδ4 : Integrable (fun ω => δ ω ^ 4) P := by
    refine hs.mono' (hδm.pow_const 4).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by have := hδ0 ω; positivity)]
    exact S7PIDC_D_pow4_le n Z n ω
  have hδ2 : Integrable (fun ω => δ ω ^ 2) P := by
    refine ((integrable_const (1 : ℝ)).add hδ4).mono' (hδm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    show ‖δ ω ^ 2‖ ≤ 1 + δ ω ^ 4
    rw [Real.norm_of_nonneg (by have := hδ0 ω; positivity)]
    nlinarith [sq_nonneg (δ ω ^ 2 - 1), sq_nonneg (δ ω)]
  refine ⟨δ, hδm, hδ0, hle, hδ2, ?_⟩
  have h4 : ∫ ω, δ ω ^ 4 ∂P ≤ 3 * κ ^ 2 / 2 ^ n := by
    calc ∫ ω, δ ω ^ 4 ∂P
        ≤ ∫ ω, ∑ κ' ∈ Finset.range (2 ^ n),
            ‖Z ((κ' + 1) * 2 ^ (n - n)) ω - Z (κ' * 2 ^ (n - n)) ω‖ ^ 4 ∂P :=
          integral_mono hδ4 hs (fun ω => S7PIDC_D_pow4_le n Z n ω)
      _ = ∑ κ' ∈ Finset.range (2 ^ n),
            ∫ ω, ‖Z ((κ' + 1) * 2 ^ (n - n)) ω - Z (κ' * 2 ^ (n - n)) ω‖ ^ 4 ∂P :=
          integral_finsetSum _ (fun k hk => hterm k (Finset.mem_range.1 hk))
      _ ≤ ∑ κ' ∈ Finset.range (2 ^ n), 3 * (κ * (1 / 2 : ℝ) ^ n) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' := Finset.mem_range.1 hk
          simp only [Nat.sub_self, pow_zero, mul_one]
          have h := hv k (k + 1) (Nat.le_succ k) (by omega)
          have e : (((k + 1 : ℕ) : ℝ) - (k : ℝ)) / (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ n := by
            push_cast; rw [add_sub_cancel_left, one_div_pow]
          rwa [e] at h
      _ = 3 * κ ^ 2 / 2 ^ n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul]
          have h4 : ((2 : ℝ) ^ n) ^ 2 * (1 / 4 : ℝ) ^ n = 1 := by
            rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]; norm_num
          field_simp
          linear_combination κ ^ 2 * h4
  have hJ := S7PIDC_sq_integral_le P (fun ω => δ ω ^ 2) hδ2 (by simpa [← pow_mul] using hδ4)
  refine hJ.trans (h4.trans' (le_of_eq ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show (δ ω ^ 2) ^ 2 = δ ω ^ 4
  ring

end HRS.MC.Sec7.S7PIDT

end
