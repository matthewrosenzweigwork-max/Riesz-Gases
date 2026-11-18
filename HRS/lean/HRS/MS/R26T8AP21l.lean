import HRS.MS.R26T8AP21k

/-!
# S8.2 local Newton layer, packet T8A.P21 (part l): arithmetic of the Leibniz sum
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A

theorem r26t8a_term_small {zn : ℝ} (hz0 : 0 < zn) (hz1 : zn ≤ 1) (s : ℝ) (i q k : ℕ) (hi : i ≤ q) (hq : q ≤ k)
    {A Ck : ℝ} (hA : 0 ≤ A) (hCk : 0 ≤ Ck) {a b c : ℝ} (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha' : a ≤ 2 ^ k) (hb : b ≤ Ck * zn ^ (-s - 2 - (i : ℝ)))
    (hc : c ≤ 2 * A * (((q - i : ℕ) : ℝ) + 1) ^ 4 * zn ^ (4 - (q - i))) :
    a * b * c ≤ 2 ^ k * Ck * (2 * A * ((k : ℝ) + 1) ^ 4) * zn ^ (-s - 2 + 4 - (q : ℝ)) := by
  have hqi : (((q - i : ℕ) : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have : q - i ≤ k := by omega
    have : ((q - i : ℕ) : ℝ) ≤ k := by exact_mod_cast this
    linarith
  have hpow : (((q - i : ℕ) : ℝ) + 1) ^ 4 ≤ ((k : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hqi 4
  have hexp : zn ^ (-s - 2 - (i : ℝ)) * zn ^ (4 - (q - i)) ≤ zn ^ (-s - 2 + 4 - (q : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hz0]
    refine Real.rpow_le_rpow_of_exponent_ge hz0 hz1 ?_
    have h1 : ((4 - (q - i) : ℕ) : ℝ) ≥ 4 - (q : ℝ) + i := by
      rcases le_total (q - i) 4 with h | h
      · rw [Nat.cast_sub h]; push_cast [Nat.cast_sub hi]; linarith
      · have : (4 - (q - i) : ℕ) = 0 := by omega
        rw [this]; push_cast
        have : ((q - i : ℕ) : ℝ) ≥ 4 := by exact_mod_cast h
        push_cast [Nat.cast_sub hi] at this
        linarith
    linarith
  have hzp : 0 ≤ zn ^ (4 - (q - i)) := by positivity
  have hzr : 0 ≤ zn ^ (-s - 2 - (i : ℝ)) := Real.rpow_nonneg hz0.le _
  calc a * b * c ≤ 2 ^ k * (Ck * zn ^ (-s - 2 - (i : ℝ))) * (2 * A * ((k : ℝ) + 1) ^ 4 * zn ^ (4 - (q - i))) := by
        refine mul_le_mul (mul_le_mul ha' hb hb0 (by positivity)) ?_ hc0 (by positivity)
        refine hc.trans ?_
        gcongr
    _ = 2 ^ k * Ck * (2 * A * ((k : ℝ) + 1) ^ 4) * (zn ^ (-s - 2 - (i : ℝ)) * zn ^ (4 - (q - i))) := by ring
    _ ≤ _ := by gcongr

theorem r26t8a_term_large {zn : ℝ} (hz1 : 1 ≤ zn) {s : ℝ} (hs : 0 ≤ s) (i q k : ℕ) (hi : i ≤ q) (hq : q ≤ k)
    {A Ck : ℝ} (hA : 0 ≤ A) (hCk : 0 ≤ Ck) {a b c : ℝ} (ha : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha' : a ≤ 2 ^ k) (hb : b ≤ Ck * zn ^ (-s - 2 - (i : ℝ)))
    (hc : c ≤ 3 * A * (((q - i : ℕ) : ℝ) + 1) ^ 2 * (1 + zn) ^ 2) :
    a * b * c ≤ 2 ^ k * Ck * (12 * A * ((k : ℝ) + 1) ^ 2) := by
  have hz0 : 0 < zn := by linarith
  have hqi : (((q - i : ℕ) : ℝ) + 1) ≤ (k : ℝ) + 1 := by
    have : q - i ≤ k := by omega
    have : ((q - i : ℕ) : ℝ) ≤ k := by exact_mod_cast this
    linarith
  have hpow : (((q - i : ℕ) : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hqi 2
  have h4 : (1 + zn) ^ 2 ≤ 4 * zn ^ 2 := by nlinarith
  have hexp : zn ^ (-s - 2 - (i : ℝ)) * zn ^ 2 ≤ 1 := by
    have : zn ^ (2 : ℕ) = zn ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast zn 2).symm
    rw [this, ← Real.rpow_add hz0]
    refine Real.rpow_le_one_of_one_le_of_nonpos hz1 ?_
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    push_cast; linarith
  have hzr : 0 ≤ zn ^ (-s - 2 - (i : ℝ)) := Real.rpow_nonneg hz0.le _
  calc a * b * c ≤ 2 ^ k * (Ck * zn ^ (-s - 2 - (i : ℝ))) * (3 * A * ((k : ℝ) + 1) ^ 2 * (4 * zn ^ 2)) := by
        refine mul_le_mul (mul_le_mul ha' hb hb0 (by positivity)) ?_ hc0 (by positivity)
        refine hc.trans ?_
        gcongr
    _ = 2 ^ k * Ck * (12 * A * ((k : ℝ) + 1) ^ 2) * (zn ^ (-s - 2 - (i : ℝ)) * zn ^ 2) := by ring
    _ ≤ 2 ^ k * Ck * (12 * A * ((k : ℝ) + 1) ^ 2) * 1 := by gcongr
    _ = _ := mul_one _

end HRS.MS.R26T8A
