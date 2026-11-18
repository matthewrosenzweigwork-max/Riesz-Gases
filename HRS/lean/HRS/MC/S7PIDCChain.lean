import Mathlib

/-!
# Packet PI-D, sub-packet `s7_PID_chain`: finite dyadic chaining

Proof of `HRS.MC.Sec7.PIDPlan.s7_PID_chain` (statement copied verbatim from `HRS/MC/S7PIDPlan.lean`).
Route: `D_j = max_{κ<2^j}` of the level-`j` increment, telescoping along the binary expansion by induction on the level,
`(∑ D_j)² ≤ (∑ (5/6)^j)(∑ (6/5)^j D_j²)`, `E D_j² ≤ (E D_j⁴)^{1/2} ≤ √Λ 2^{-j/2}`, and the geometric sums
`∑ (5/6)^j ≤ 6`, `∑ (6√(1/2)/5)^j ≤ 20/3`.  If some increment has a non-integrable fourth power, the Lean integral
convention makes the bound trivial for `S = ∑ D_j + Δ²`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDC

/-- Jensen for the square on a probability space. -/
theorem S7PIDC_sq_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (h1 : Integrable X P) (h2 : Integrable (fun ω => X ω ^ 2) P) :
    (∫ ω, X ω ∂P) ^ 2 ≤ ∫ ω, X ω ^ 2 ∂P := by
  set m := ∫ ω, X ω ∂P with hm
  have h3 : Integrable (fun ω => X ω ^ 2 + m ^ 2) P := h2.add (integrable_const _)
  have h4 : Integrable (fun ω => 2 * m * X ω) P := h1.const_mul _
  have h5 := integral_mono h4 h3 (fun ω => by nlinarith [sq_nonneg (X ω - m)])
  rw [integral_const_mul, integral_add h2 (integrable_const _), integral_const] at h5
  simp only [probReal_univ, one_smul] at h5
  rw [← hm] at h5
  nlinarith

/-- Geometric sums are bounded by `1/(1-x)`. -/
theorem S7PIDC_geom_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, x ^ j ≤ 1 / (1 - x) := by
  have h := geom_sum_mul_neg x N
  have hpos : 0 < 1 - x := by linarith
  rw [le_div_iff₀ hpos]
  have : 0 ≤ x ^ N := pow_nonneg hx0 N
  nlinarith

/-- Telescoping along the binary expansion: induction on the level. -/
theorem S7PIDC_telescope {E : Type*} [NormedAddCommGroup E] (n : ℕ) (g : ℕ → E) (D : ℕ → ℝ)
    (hD : ∀ j, 0 ≤ D j)
    (hinc : ∀ j ≤ n, ∀ k < 2 ^ j, ‖g ((k + 1) * 2 ^ (n - j)) - g (k * 2 ^ (n - j))‖ ≤ D j) :
    ∀ k ≤ 2 ^ n, ‖g k - g 0‖ ≤ ∑ j ∈ Finset.range (n + 1), D j := by
  have key : ∀ m ≤ n, ∀ i ≤ 2 ^ m, ‖g (i * 2 ^ (n - m)) - g 0‖ ≤ ∑ j ∈ Finset.range (m + 1), D j := by
    intro m
    induction m with
    | zero =>
      intro hm i hi
      simp only [pow_zero] at hi
      interval_cases i
      · simpa using hD 0
      · have := hinc 0 hm 0 (by simp)
        simpa using this
    | succ m ih =>
      intro hm i hi
      have hnm : n - m = (n - (m + 1)) + 1 := by omega
      have hi' := hi
      rw [pow_succ] at hi'
      rcases Nat.even_or_odd' i with ⟨i', rfl | rfl⟩
      · have e : 2 * i' * 2 ^ (n - (m + 1)) = i' * 2 ^ (n - m) := by
          rw [hnm, pow_succ]; ring
        rw [e]
        refine (ih (by omega) i' (by omega)).trans ?_
        rw [Finset.sum_range_succ _ (m + 1)]
        linarith [hD (m + 1)]
      · have h1 := ih (by omega) i' (by omega)
        have h2 := hinc (m + 1) hm (2 * i') (by omega)
        have e : 2 * i' * 2 ^ (n - (m + 1)) = i' * 2 ^ (n - m) := by
          rw [hnm, pow_succ]; ring
        have e' : (2 * i' + 1) * 2 ^ (n - (m + 1)) = (2 * i' + 1) * 2 ^ (n - (m + 1)) := rfl
        rw [e] at h2
        calc ‖g ((2 * i' + 1) * 2 ^ (n - (m + 1))) - g 0‖
            ≤ ‖g ((2 * i' + 1) * 2 ^ (n - (m + 1))) - g (i' * 2 ^ (n - m))‖
                + ‖g (i' * 2 ^ (n - m)) - g 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ D (m + 1) + ∑ j ∈ Finset.range (m + 1), D j := by
              have h2' : ‖g ((2 * i' + 1) * 2 ^ (n - (m + 1))) - g (i' * 2 ^ (n - m))‖ ≤ D (m + 1) := by
                have : (2 * i' + 1) * 2 ^ (n - (m + 1)) = (2 * i' + 1) * 2 ^ (n - (m + 1)) := rfl
                exact h2
              linarith
          _ = ∑ j ∈ Finset.range (m + 1 + 1), D j := by
              rw [Finset.sum_range_succ _ (m + 1)]; ring
  intro k hk
  have := key n le_rfl k hk
  simpa using this

theorem S7PIDC_ne (j : ℕ) : (Finset.range (2 ^ j)).Nonempty :=
  ⟨0, Finset.mem_range.2 (Nat.two_pow_pos j)⟩

/-- The level-`j` maximal increment. -/
def S7PIDC_D {E : Type*} [NormedAddCommGroup E] {Ω : Type*} (n : ℕ) (Y : ℕ → Ω → E) (j : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (2 ^ j)).sup' (S7PIDC_ne j)
    (fun κ => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖)

theorem S7PIDC_D_nonneg {E : Type*} [NormedAddCommGroup E] {Ω : Type*} (n : ℕ) (Y : ℕ → Ω → E) (j : ℕ)
    (ω : Ω) : 0 ≤ S7PIDC_D n Y j ω := by
  unfold S7PIDC_D
  exact le_trans (norm_nonneg _) (Finset.le_sup' (fun κ => ‖Y ((κ + 1) * 2 ^ (n - j)) ω -
    Y (κ * 2 ^ (n - j)) ω‖) (Finset.mem_range.2 (Nat.two_pow_pos j)))

theorem S7PIDC_D_le {E : Type*} [NormedAddCommGroup E] {Ω : Type*} (n : ℕ) (Y : ℕ → Ω → E) (j : ℕ)
    (ω : Ω) (κ : ℕ) (hκ : κ < 2 ^ j) :
    ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ≤ S7PIDC_D n Y j ω := by
  unfold S7PIDC_D
  exact Finset.le_sup' (fun κ => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖)
    (Finset.mem_range.2 hκ)

theorem S7PIDC_D_meas {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (Y : ℕ → Ω → E) (hY : ∀ a b, Measurable fun ω => ‖Y a ω - Y b ω‖) (j : ℕ) :
    Measurable (S7PIDC_D n Y j) := by
  unfold S7PIDC_D
  have := Finset.measurable_sup' (δ := Ω) (s := Finset.range (2 ^ j))
    (S7PIDC_ne j)
    (f := fun κ ω => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖)
    (fun κ _ => hY _ _)
  convert this using 1
  ext ω
  exact (Finset.sup'_apply (C := fun _ : Ω => ℝ) (S7PIDC_ne j) (fun κ ω => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖) ω).symm

theorem S7PIDC_D_pow4_le {E : Type*} [NormedAddCommGroup E] {Ω : Type*} (n : ℕ) (Y : ℕ → Ω → E) (j : ℕ)
    (ω : Ω) :
    S7PIDC_D n Y j ω ^ 4 ≤ ∑ κ ∈ Finset.range (2 ^ j),
      ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4 := by
  obtain ⟨κ, hκ, heq⟩ := Finset.exists_mem_eq_sup'
    (S7PIDC_ne j)
    (fun κ => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖)
  have : S7PIDC_D n Y j ω = ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ := heq
  rw [this]
  exact Finset.single_le_sum (f := fun κ => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4)
    (fun _ _ => by positivity) hκ

/-- **D3 (finite dyadic chaining)** (statement verbatim from `S7PIDPlan.lean`). -/
theorem s7_PID_chain_proof {E : Type*} [NormedAddCommGroup E] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (Y : ℕ → Ω → E) (hY : ∀ a b, Measurable fun ω => ‖Y a ω - Y b ω‖) (Λ : ℝ)
    (hinc : ∀ j ≤ n, ∀ k < 2 ^ j,
      ∫ ω, ‖Y ((k + 1) * 2 ^ (n - j)) ω - Y (k * 2 ^ (n - j)) ω‖ ^ 4 ∂P ≤ Λ * (1 / 4 : ℝ) ^ j) :
    ∃ S : Ω → ℝ, Measurable S ∧ (∀ ω, ∀ k ≤ 2 ^ n, ‖Y k ω - Y 0 ω‖ ≤ S ω) ∧
      ∫ ω, S ω ^ 2 ∂P ≤ 40 * Real.sqrt Λ := by
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
  by_cases hint : ∀ j ≤ n, ∀ κ < 2 ^ j,
      Integrable (fun ω => ‖Y ((κ + 1) * 2 ^ (n - j)) ω - Y (κ * 2 ^ (n - j)) ω‖ ^ 4) P
  · refine ⟨fun ω => ∑ j ∈ Finset.range (n + 1), D j ω, hSm, hbound, ?_⟩
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
    refine hmain.trans ?_
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
  · push Not at hint
    obtain ⟨j0, hj0, κ0, hκ0, hni⟩ := hint
    set Δ : Ω → ℝ := fun ω => ‖Y ((κ0 + 1) * 2 ^ (n - j0)) ω - Y (κ0 * 2 ^ (n - j0)) ω‖ with hΔ
    have hΔm : Measurable Δ := hY _ _
    refine ⟨fun ω => ∑ j ∈ Finset.range (n + 1), D j ω + Δ ω ^ 2, hSm.add (hΔm.pow_const 2), ?_, ?_⟩
    · intro ω k hk
      have := hbound ω k hk
      have : 0 ≤ Δ ω ^ 2 := sq_nonneg _
      linarith [hbound ω k hk]
    · have hnot : ¬ Integrable (fun ω => (∑ j ∈ Finset.range (n + 1), D j ω + Δ ω ^ 2) ^ 2) P := by
        intro hI
        apply hni
        refine hI.mono' ((hΔm.pow_const 4).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
        have h1 : 0 ≤ ∑ j ∈ Finset.range (n + 1), D j ω := Finset.sum_nonneg (fun j _ => hD0 j ω)
        have h2 : 0 ≤ Δ ω ^ 2 := sq_nonneg _
        rw [Real.norm_of_nonneg (by positivity)]
        show Δ ω ^ 4 ≤ _
        have : Δ ω ^ 4 = (Δ ω ^ 2) ^ 2 := by ring
        rw [this]
        nlinarith
      rw [integral_undef hnot]
      positivity

end HRS.MC.Sec7.S7PIDC

end
