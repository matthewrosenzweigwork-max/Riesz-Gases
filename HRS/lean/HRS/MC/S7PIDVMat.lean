import HRS.MC.S7PIEStrong

/-!
# Packet PI-D, sub-packet V (helper): matrix and sequence lemmas

* `S7PIDV_finBd_sub`, `S7PIDV_finBd_id`, `S7PIDV_pieWmat_sub`: finite-section bounds of differences and of the identity;
* `S7PIDV_holder_seq`: the Hölder-`1/2` estimate `E_{m-1} → E_m` of a transposed matrix action from the two bounds
  `E_{m-2} → E_m` (norm `ℓ`) and `E_m → E_m` (norm `B`), by an elementary frequency cutoff at `N = √(B/ℓ)`:
  the low part costs `ℓ N`, the high part `B / N`, so the squared norm is `≤ 4 ℓ B`.
-/

open Finset

noncomputable section

namespace HRS.MC.Sec7.S7PIDV

open HRS.MC.Sec7.PIE

lemma S7PIDV_pieWmat_sub {ι : Type*} (w : ι → ℝ) (T1 T2 : ι → ι → ℝ) (σ : ℝ) :
    pieWmat w (fun j k => T1 j k - T2 j k) σ = fun j k => pieWmat w T1 σ j k - pieWmat w T2 σ j k := by
  funext j k
  simp only [pieWmat]
  ring

lemma S7PIDV_finBd_sub {ι : Type*} {S1 S2 : ι → ι → ℝ} {A1 A2 : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2)
    (h1 : pieFinBd S1 A1) (h2 : pieFinBd S2 A2) : pieFinBd (fun j k => S1 j k - S2 j k) (2 * (A1 + A2)) := by
  intro K J x
  have e1 := h1 K J x
  have e2 := h2 K J x
  have hX : 0 ≤ ∑ k ∈ K, x k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hpt : ∀ j, (∑ k ∈ K, (S1 j k - S2 j k) * x k) ^ 2 ≤
      2 * (∑ k ∈ K, S1 j k * x k) ^ 2 + 2 * (∑ k ∈ K, S2 j k * x k) ^ 2 := by
    intro j
    have : ∑ k ∈ K, (S1 j k - S2 j k) * x k = ∑ k ∈ K, S1 j k * x k - ∑ k ∈ K, S2 j k * x k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    nlinarith [sq_nonneg (∑ k ∈ K, S1 j k * x k + ∑ k ∈ K, S2 j k * x k)]
  calc ∑ j ∈ J, (∑ k ∈ K, (S1 j k - S2 j k) * x k) ^ 2
      ≤ ∑ j ∈ J, (2 * (∑ k ∈ K, S1 j k * x k) ^ 2 + 2 * (∑ k ∈ K, S2 j k * x k) ^ 2) :=
        Finset.sum_le_sum fun j _ => hpt j
    _ = 2 * ∑ j ∈ J, (∑ k ∈ K, S1 j k * x k) ^ 2 + 2 * ∑ j ∈ J, (∑ k ∈ K, S2 j k * x k) ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (A1 ^ 2 * ∑ k ∈ K, x k ^ 2) + 2 * (A2 ^ 2 * ∑ k ∈ K, x k ^ 2) := by gcongr
    _ ≤ (2 * (A1 + A2)) ^ 2 * ∑ k ∈ K, x k ^ 2 := by
        nlinarith [mul_nonneg hA1 hA2, mul_nonneg (mul_nonneg hA1 hA2) hX, sq_nonneg A1, sq_nonneg A2,
          mul_nonneg (sq_nonneg A1) hX, mul_nonneg (sq_nonneg A2) hX]

lemma S7PIDV_finBd_id {ι : Type*} [DecidableEq ι] : pieFinBd (fun j k : ι => if j = k then (1 : ℝ) else 0) 1 := by
  intro K J x
  have e : ∀ j, (∑ k ∈ K, (if j = k then (1 : ℝ) else 0) * x k) ^ 2 = if j ∈ K then x j ^ 2 else 0 := by
    intro j
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  simp_rw [e]
  rw [Finset.sum_ite_mem, one_pow, one_mul]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun k _ _ => sq_nonneg _

/-- Hölder-`1/2` interpolation by a frequency cutoff. -/
theorem S7PIDV_holder_seq {ι : Type*} {w : ι → ℝ} (hw1 : ∀ i, 1 ≤ w i) {Δ : ι → ι → ℝ} {m ℓ B : ℝ}
    (hℓ : 0 < ℓ) (hB : 0 < B)
    (h2 : pieFinBd (pieWmat w (fun j k => w j ^ (-(2 : ℝ)) * Δ j k) m) ℓ)
    (h0 : pieFinBd (pieWmat w Δ m) B) (a : ι → ℝ)
    (ha : Summable fun j => (w j ^ (-(m - 1)) * a j) ^ 2) :
    Summable (fun k => (w k ^ (-m) * ∑' j, a j * Δ j k) ^ 2) ∧
      ∑' k, (w k ^ (-m) * ∑' j, a j * Δ j k) ^ 2 ≤ 4 * ℓ * B * ∑' j, (w j ^ (-(m - 1)) * a j) ^ 2 := by
  classical
  have hw : ∀ i, 0 < w i := fun i => lt_of_lt_of_le one_pos (hw1 i)
  have hBl : 0 < B / ℓ := div_pos hB hℓ
  set N : ℝ := Real.sqrt (B / ℓ) with hNdef
  have hN : 0 < N := Real.sqrt_pos.2 hBl
  have hN2 : N ^ 2 = B / ℓ := Real.sq_sqrt hBl.le
  set c : ι → ℝ := fun j => w j ^ (-(m - 1)) * a j with hc
  set S : ℝ := ∑' j, c j ^ 2 with hS
  let aK : ι → ℝ := fun j => if w j ≤ N then a j else 0
  let bK : ι → ℝ := fun j => if w j ≤ N then 0 else a j
  have hab : ∀ j, a j = aK j + bK j := by
    intro j; simp only [aK, bK]; split_ifs <;> simp
  let aK2 : ι → ℝ := fun j => w j ^ (2 : ℝ) * aK j
  have hrp1 : ∀ j, w j ^ (-m) * w j ^ (2 : ℝ) = w j * w j ^ (-(m - 1)) := by
    intro j
    have h1 : w j * w j ^ (-(m - 1)) = w j ^ (1 : ℝ) * w j ^ (-(m - 1)) := by rw [Real.rpow_one]
    rw [h1, ← Real.rpow_add (hw j), ← Real.rpow_add (hw j)]
    congr 1; ring
  have hrp2 : ∀ j, w j ^ (-m) = (w j)⁻¹ * w j ^ (-(m - 1)) := by
    intro j
    have h1 : (w j)⁻¹ = w j ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
    rw [h1, ← Real.rpow_add (hw j)]
    congr 1; ring
  have hww : ∀ j, w j ^ (2 : ℝ) * w j ^ (-(2 : ℝ)) = 1 := by
    intro j; rw [← Real.rpow_add (hw j)]; simp
  -- pointwise bounds
  have hA2 : ∀ j, (w j ^ (-m) * aK2 j) ^ 2 ≤ N ^ 2 * c j ^ 2 := by
    intro j
    by_cases hj : w j ≤ N
    · have : w j ^ (-m) * aK2 j = w j * c j := by
        simp only [aK2, aK, hj, ite_true, hc]
        rw [← mul_assoc, hrp1 j]; ring
      rw [this, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hw j).le hj 2) (sq_nonneg _)
    · simp only [aK2, aK, hj, ite_false, mul_zero]
      rw [zero_pow two_ne_zero]; positivity
  have hQ : ∀ j, (w j ^ (-m) * bK j) ^ 2 ≤ (N ^ 2)⁻¹ * c j ^ 2 := by
    intro j
    by_cases hj : w j ≤ N
    · simp only [bK, hj, ite_true, mul_zero]
      rw [zero_pow two_ne_zero]; positivity
    · have hj' : N < w j := not_le.1 hj
      have : w j ^ (-m) * bK j = (w j)⁻¹ * c j := by
        simp only [bK, hj, ite_false, hc]
        rw [hrp2 j]; ring
      rw [this, mul_pow, inv_pow]
      have : (w j ^ 2)⁻¹ ≤ (N ^ 2)⁻¹ := by
        gcongr
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hgen : ∀ j, (w j ^ (-m) * a j) ^ 2 ≤ c j ^ 2 := by
    intro j
    have : w j ^ (-m) * a j = (w j)⁻¹ * c j := by simp only [hc]; rw [hrp2 j]; ring
    rw [this, mul_pow, inv_pow]
    have h1 : (w j ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by have := hw j; positivity)]
      nlinarith [hw1 j]
    calc (w j ^ 2)⁻¹ * c j ^ 2 ≤ 1 * c j ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = c j ^ 2 := one_mul _
  have hcs : Summable fun j => c j ^ 2 := ha
  have haKm : ∀ j, (w j ^ (-m) * aK j) ^ 2 ≤ c j ^ 2 := by
    intro j
    by_cases hj : w j ≤ N
    · simp only [aK, hj, ite_true]; exact hgen j
    · simp only [aK, hj, ite_false, mul_zero]; rw [zero_pow two_ne_zero]; positivity
  have hbKm : ∀ j, (w j ^ (-m) * bK j) ^ 2 ≤ c j ^ 2 := by
    intro j
    by_cases hj : w j ≤ N
    · simp only [bK, hj, ite_true, mul_zero]; rw [zero_pow two_ne_zero]; positivity
    · simp only [bK, hj, ite_false]; exact hgen j
  have hsaK2 : Summable fun j => (w j ^ (-m) * aK2 j) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hA2 (hcs.mul_left _)
  have hsbK : Summable fun j => (w j ^ (-m) * bK j) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hQ (hcs.mul_left _)
  have hsaKm : Summable fun j => (w j ^ (-m) * aK j) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) haKm hcs
  have hsbKm : Summable fun j => (w j ^ (-m) * bK j) ^ 2 :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hbKm hcs
  have hsumA2 : ∑' j, (w j ^ (-m) * aK2 j) ^ 2 ≤ N ^ 2 * S :=
    (Summable.tsum_le_tsum hA2 hsaK2 (hcs.mul_left _)).trans (le_of_eq (tsum_mul_left))
  have hsumQ : ∑' j, (w j ^ (-m) * bK j) ^ 2 ≤ (N ^ 2)⁻¹ * S :=
    (Summable.tsum_le_tsum hQ hsbK (hcs.mul_left _)).trans (le_of_eq (tsum_mul_left))
  -- the two pieces
  obtain ⟨hPs, hPb⟩ := pie_dual hw hℓ.le h2 aK2 hsaK2
  obtain ⟨hQs, hQb⟩ := pie_dual hw hB.le h0 bK hsbK
  have hPeq : ∀ k, ∑' j, aK2 j * (w j ^ (-(2 : ℝ)) * Δ j k) = ∑' j, aK j * Δ j k := by
    intro k
    refine tsum_congr fun j => ?_
    simp only [aK2]
    calc w j ^ (2 : ℝ) * aK j * (w j ^ (-(2 : ℝ)) * Δ j k)
        = (w j ^ (2 : ℝ) * w j ^ (-(2 : ℝ))) * (aK j * Δ j k) := by ring
      _ = aK j * Δ j k := by rw [hww j, one_mul]
  have hrow : ∀ k, ∑' j, a j * Δ j k = ∑' j, aK j * Δ j k + ∑' j, bK j * Δ j k := by
    intro k
    rw [← Summable.tsum_add (pie_row_summable hw h0 aK hsaKm k) (pie_row_summable hw h0 bK hsbKm k)]
    refine tsum_congr fun j => ?_
    rw [← add_mul, ← hab j]
  simp_rw [hPeq] at hPs hPb
  have hdecomp : ∀ k, w k ^ (-m) * ∑' j, a j * Δ j k =
      w k ^ (-m) * ∑' j, aK j * Δ j k + w k ^ (-m) * ∑' j, bK j * Δ j k := by
    intro k; rw [hrow k, mul_add]
  simp_rw [hdecomp]
  obtain ⟨hsum, hle⟩ := pie_summable_add_sq hPs hQs
  refine ⟨hsum, hle.trans ?_⟩
  have hS0 : 0 ≤ S := tsum_nonneg fun j => sq_nonneg _
  have hN2pos : 0 < N ^ 2 := by positivity
  have e1 : ℓ ^ 2 * (N ^ 2 * S) = ℓ * B * S := by
    rw [hN2]; field_simp
  have e2 : B ^ 2 * ((N ^ 2)⁻¹ * S) = ℓ * B * S := by
    rw [hN2]; field_simp
  have h1 : ∑' k, (w k ^ (-m) * ∑' j, aK j * Δ j k) ^ 2 ≤ ℓ * B * S := by
    refine hPb.trans ?_
    rw [← e1]
    exact mul_le_mul_of_nonneg_left hsumA2 (sq_nonneg _)
  have h2' : ∑' k, (w k ^ (-m) * ∑' j, bK j * Δ j k) ^ 2 ≤ ℓ * B * S := by
    refine hQb.trans ?_
    rw [← e2]
    exact mul_le_mul_of_nonneg_left hsumQ (sq_nonneg _)
  show 2 * _ + 2 * _ ≤ 4 * ℓ * B * S
  nlinarith [h1, h2']

end HRS.MC.Sec7.S7PIDV

end
