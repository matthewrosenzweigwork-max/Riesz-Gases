import HRS.MS.SA12X2R36S4

/-!
# S.A.12 R36 (SA12X3), part S5A: the scale choice and the sum bound

* `sa12x2_r_choice`: the ε-distribution: a scale `r ≤ 1` with `X Cn r^g ≤ ν₀/(8e)` and
  `X Cn r^g + X C₁ r^{-θ} ≤ C (1 + ν₀^{-(θ/g)})`, `C` independent of `ν₀`.
* `sa12x2_sum_bound`: summing the per-term bounds over `(j, idx, i, l)` with `|M| ≤ MB`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x2_r_choice {g θ X Cn C1 e : ℝ} (hg : 0 < g) (hθ : 0 ≤ θ) (hX : 0 ≤ X) (hCn : 0 ≤ Cn)
    (hC1 : 0 ≤ C1) (he : 1 ≤ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν0 : ℝ, 0 < ν0 → ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ X * Cn * r ^ g ≤ ν0 / (8 * e) ∧
      X * Cn * r ^ g + X * C1 * r ^ (-θ) ≤ C * (1 + ν0 ^ (-(θ / g))) := by
  set Z : ℝ := 8 * e * (X * Cn + 1) with hZ
  have hXC : 0 ≤ X * Cn := mul_nonneg hX hCn
  have hZpos : 0 < Z := by rw [hZ]; positivity
  set Q : ℝ := Z ^ (θ / g) with hQ
  have hQ0 : 0 ≤ Q := Real.rpow_nonneg hZpos.le _
  refine ⟨X * Cn + X * C1 * (1 + Q), by positivity, fun ν0 hν0 => ?_⟩
  set ρ : ℝ := (ν0 / Z) ^ (1 / g) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos (div_pos hν0 hZpos) _
  refine ⟨min 1 ρ, lt_min one_pos hρpos, min_le_left _ _, ?_, ?_⟩
  · have h1 : (min 1 ρ) ^ g ≤ ρ ^ g :=
      Real.rpow_le_rpow (lt_min one_pos hρpos).le (min_le_right _ _) hg.le
    have h2 : ρ ^ g = ν0 / Z := by
      rw [hρ, ← Real.rpow_mul (div_pos hν0 hZpos).le, one_div_mul_cancel hg.ne', Real.rpow_one]
    rw [h2] at h1
    calc X * Cn * (min 1 ρ) ^ g ≤ X * Cn * (ν0 / Z) := mul_le_mul_of_nonneg_left h1 hXC
      _ ≤ ν0 / (8 * e) := by
        rw [hZ, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hν0.le (mul_nonneg hXC (by linarith : (0 : ℝ) ≤ e))]
  · have hr1 : (min 1 ρ) ^ g ≤ 1 := Real.rpow_le_one (lt_min one_pos hρpos).le (min_le_left _ _) hg.le
    have hρθ : ρ ^ (-θ) = Q * ν0 ^ (-(θ / g)) := by
      rw [hρ, ← Real.rpow_mul (div_pos hν0 hZpos).le]
      have e1 : 1 / g * -θ = -(θ / g) := by ring
      rw [e1, Real.rpow_neg (div_pos hν0 hZpos).le, Real.div_rpow hν0.le hZpos.le, inv_div,
        Real.rpow_neg hν0.le, hQ, div_eq_mul_inv]
    have hrθ : (min 1 ρ) ^ (-θ) ≤ 1 + Q * ν0 ^ (-(θ / g)) := by
      rcases le_total 1 ρ with h | h
      · rw [min_eq_left h, Real.one_rpow]
        have : 0 ≤ Q * ν0 ^ (-(θ / g)) := mul_nonneg hQ0 (Real.rpow_nonneg hν0.le _)
        linarith
      · rw [min_eq_right h, hρθ]
        linarith
    have hν : 0 ≤ ν0 ^ (-(θ / g)) := Real.rpow_nonneg hν0.le _
    have e2 := mul_le_mul_of_nonneg_left hr1 hXC
    have e3 := mul_le_mul_of_nonneg_left hrθ (mul_nonneg hX hC1)
    have e4 : 0 ≤ X * C1 * (Q * ν0 ^ (-(θ / g))) := by positivity
    have hA : 0 ≤ X * C1 * Q := mul_nonneg (mul_nonneg hX hC1) hQ0
    nlinarith [mul_nonneg hA hν, mul_nonneg hXC hν, mul_nonneg (mul_nonneg hX hC1) hν]

/-- Summing the per-term bounds. -/
theorem sa12x2_sum_bound {m : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} {MB P : ℝ} (hM : ∀ i j, |M i j| ≤ MB)
    (_hP : 0 ≤ P) (T : (j : ℕ) → (Fin j → Fin d) → Fin d → Fin d → ℝ)
    (hT : ∀ j ≤ m, ∀ idx i l, |T j idx i l| ≤ P) :
    -(2 * ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d,
        M l i * T j idx i l) ≤
      2 * (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * ((d : ℝ) * d))) * max MB 0 * P := by
  have hMB : ∀ i l, |M l i| ≤ max MB 0 := fun i l => (hM l i).trans (le_max_left _ _)
  have hterm : ∀ j ≤ m, ∀ idx i l, M l i * T j idx i l ≤ max MB 0 * P := by
    intro j hj idx i l
    calc M l i * T j idx i l ≤ |M l i * T j idx i l| := le_abs_self _
      _ = |M l i| * |T j idx i l| := abs_mul _ _
      _ ≤ max MB 0 * P := mul_le_mul (hMB i l) (hT j hj idx i l) (abs_nonneg _) (le_max_right _ _)
  have hj : ∀ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d,
        M l i * T j idx i l ≥ -((Nat.choose m j : ℝ) * ((d : ℝ) ^ j * ((d : ℝ) * d)) * (max MB 0 * P)) := by
    intro j hjm
    have hjle : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjm)
    have hlow : ∀ idx i l, -(max MB 0 * P) ≤ M l i * T j idx i l := by
      intro idx i l
      have h1 : |M l i * T j idx i l| ≤ max MB 0 * P := by
        rw [abs_mul]
        exact mul_le_mul (hMB i l) (hT j hjle idx i l) (abs_nonneg _) (le_max_right _ _)
      linarith [neg_abs_le (M l i * T j idx i l)]
    have hs : -((d : ℝ) ^ j * ((d : ℝ) * d) * (max MB 0 * P)) ≤
        ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d, M l i * T j idx i l := by
      have h2 : ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d, (-(max MB 0 * P)) ≤
          ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d, M l i * T j idx i l :=
        Finset.sum_le_sum fun idx _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hlow idx i l
      have h3 : ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d, (-(max MB 0 * P)) =
          -((d : ℝ) ^ j * ((d : ℝ) * d) * (max MB 0 * P)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
      linarith
    have hc : (0 : ℝ) ≤ Nat.choose m j := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left hs hc
    linarith
  have hsum := Finset.sum_le_sum hj
  have hlow2 : ∑ j ∈ Finset.range (m + 1), -((Nat.choose m j : ℝ) * ((d : ℝ) ^ j * ((d : ℝ) * d)) * (max MB 0 * P)) =
      -((∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * ((d : ℝ) * d))) * (max MB 0 * P)) := by
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  rw [hlow2] at hsum
  nlinarith [hsum]

end HRS.MH.AdjointRd.Phase2SA12Near
