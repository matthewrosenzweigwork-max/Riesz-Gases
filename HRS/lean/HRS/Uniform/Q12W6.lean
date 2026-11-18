import HRS.Uniform.Q12W5

/-!
# Q12, part W6: the real-variable bookkeeping of Lemma 3.23 and the conditional proof of `energy_W2`
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_max_sub (q : ℝ) : max 2 q - max (q - 2) 0 = 2 := by
  rcases le_total q 2 with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- `t^{-q'/2} E' ≤ E^{2/p}` for `t ≥ E^{2/p}`, `0 ≤ E' ≤ E`. -/
lemma q12_tpow_mul_le {q E E' t : ℝ} (hE : 0 < E) (hE' : 0 ≤ E') (hEE : E' ≤ E)
    (ht : E ^ (2 / max 2 q) ≤ t) :
    t ^ (-(max (q - 2) 0) / 2) * E' ≤ E ^ (2 / max 2 q) := by
  set p : ℝ := max 2 q with hp
  set q' : ℝ := max (q - 2) 0 with hq'
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hq'0 : 0 ≤ q' := le_max_right _ _
  have hEp : 0 < E ^ (2 / p) := Real.rpow_pos_of_pos hE _
  have h1 : t ^ (-q' / 2) ≤ (E ^ (2 / p)) ^ (-q' / 2) := by
    apply Real.rpow_le_rpow_of_nonpos hEp ht
    have : 0 ≤ q' / 2 := by positivity
    rw [neg_div]; linarith
  have h2 : (E ^ (2 / p)) ^ (-q' / 2) = E ^ (-q' / p) := by
    rw [← Real.rpow_mul hE.le]; congr 1; field_simp
  have h3 : E ^ (-q' / p) * E = E ^ (2 / p) := by
    have e1 : E ^ (-q' / p) * E = E ^ (-q' / p) * E ^ (1 : ℝ) := by rw [Real.rpow_one]
    rw [e1, ← Real.rpow_add hE]
    congr 1
    have := q12_max_sub q
    rw [← hp, ← hq'] at this
    field_simp
    linarith
  calc t ^ (-q' / 2) * E' ≤ (E ^ (2 / p)) ^ (-q' / 2) * E := by
        refine mul_le_mul h1 hEE hE' (Real.rpow_nonneg hEp.le _)
    _ = E ^ (2 / p) := by rw [h2, h3]

theorem q12_final_bound {dd Cp m Kh : ℝ} (hdd : 0 ≤ dd) (hCp : 0 < Cp) (hm : 0 < m) (hKh : 0 ≤ Kh)
    {lam v E E' : ℝ} (q : ℝ) (hlam : 0 < lam) (hlv : lam ≤ v) (hE0 : 0 ≤ E') (hEE : E' ≤ E) :
    2 * Real.sqrt (dd * max (2 * lam ^ 2) (E ^ (2 / max 2 q)) / 8) +
      Cp / Real.sqrt m * Real.sqrt (Kh * max (2 * lam ^ 2) (E ^ (2 / max 2 q)) ^
        (-(max (q - 2) 0) / 2) * (2 * E')) ≤
    (2 * Real.sqrt (dd / 8) * (Real.sqrt 2 + 1) + Cp / Real.sqrt m * Real.sqrt (2 * Kh) + 1) *
      (v + E ^ (1 / max 2 q)) := by
  set p : ℝ := max 2 q with hp
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hE : 0 ≤ E := le_trans hE0 hEE
  set u : ℝ := E ^ (1 / p) with hu
  have hu0 : 0 ≤ u := Real.rpow_nonneg hE _
  have hv0 : 0 ≤ v := le_trans hlam.le hlv
  set t : ℝ := max (2 * lam ^ 2) (E ^ (2 / p)) with ht
  have hu2 : u ^ 2 = E ^ (2 / p) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hE]; congr 1; push_cast; field_simp
  have ht1 : t ≤ 2 * lam ^ 2 + u ^ 2 := by
    rw [hu2]; exact max_le (by nlinarith [Real.rpow_nonneg hE (2 / p)]) (by nlinarith [sq_nonneg lam])
  have ht0 : 0 ≤ t := le_trans (by positivity) (le_max_left _ _)
  have hsq : Real.sqrt t ≤ Real.sqrt 2 * v + u := by
    rw [Real.sqrt_le_left (by positivity)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [mul_nonneg hu0 (mul_nonneg (Real.sqrt_nonneg 2) hv0), mul_self_le_mul_self hlam.le hlv,
      Real.sqrt_nonneg 2]
  -- first term
  have hA : 2 * Real.sqrt (dd * t / 8) ≤ 2 * Real.sqrt (dd / 8) * (Real.sqrt 2 + 1) * (v + u) := by
    have : Real.sqrt (dd * t / 8) = Real.sqrt (dd / 8) * Real.sqrt t := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
    rw [this]
    have h1 : Real.sqrt 2 * v + u ≤ (Real.sqrt 2 + 1) * (v + u) := by
      nlinarith [Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) hu0]
    have h0 : 0 ≤ Real.sqrt (dd / 8) := Real.sqrt_nonneg _
    calc 2 * (Real.sqrt (dd / 8) * Real.sqrt t) = 2 * Real.sqrt (dd / 8) * Real.sqrt t := by ring
      _ ≤ 2 * Real.sqrt (dd / 8) * ((Real.sqrt 2 + 1) * (v + u)) :=
          mul_le_mul_of_nonneg_left (hsq.trans h1) (by positivity)
      _ = _ := by ring
  -- second term
  have hB : Real.sqrt (Kh * t ^ (-(max (q - 2) 0) / 2) * (2 * E')) ≤ Real.sqrt (2 * Kh) * u := by
    rcases hE.eq_or_lt with h0 | hpos
    · have : E' = 0 := le_antisymm (h0 ▸ hEE) hE0
      rw [this]; simp
      positivity
    · have h1 := q12_tpow_mul_le (q := q) hpos hE0 hEE (le_max_right (2 * lam ^ 2) _)
      rw [Real.sqrt_le_left (by positivity)]
      have h2 : 0 ≤ Kh := hKh
      calc Kh * t ^ (-(max (q - 2) 0) / 2) * (2 * E') = (2 * Kh) * (t ^ (-(max (q - 2) 0) / 2) * E') := by ring
        _ ≤ (2 * Kh) * u ^ 2 := by rw [hu2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (Real.sqrt (2 * Kh) * u) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hB' : Cp / Real.sqrt m * Real.sqrt (Kh * t ^ (-(max (q - 2) 0) / 2) * (2 * E')) ≤
      Cp / Real.sqrt m * Real.sqrt (2 * Kh) * u := by
    calc _ ≤ Cp / Real.sqrt m * (Real.sqrt (2 * Kh) * u) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hX : 0 ≤ Cp / Real.sqrt m * Real.sqrt (2 * Kh) := by positivity
  have hY : 0 ≤ 2 * Real.sqrt (dd / 8) * (Real.sqrt 2 + 1) := by positivity
  nlinarith [mul_nonneg hX (add_nonneg hv0 hu0), mul_nonneg hX hv0, mul_nonneg hX hu0]

end HRS.Uniform.Q12
