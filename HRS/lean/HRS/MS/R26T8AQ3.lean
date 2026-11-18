import HRS.MS.R26T8AQ2
import HRS.MS.R26T8AShear4
import HRS.MS.R26T8AP11sn
import HRS.MS.R26T8AP11jc
import HRS.MS.R26T8AP11wt
import HRS.MS.R26T8AP11e

/-!
# S8.2 Taylor split (Q), step 3: nested jets of the local Riesz potential of a smooth function
`r26t8a_Vg_near`: `‖nest p q (Wg ∘ S_{-1/2}) X z‖ <= C Bs jb(X)^(2M)` for `|z| <= 4`.
`r26t8a_localRiesz_smooth_jets`: if `‖nest p q (midPair P)‖ <= B pairWeight` for `p+q <= k` and `P` is `C^k`, then
`‖nest p q (midPair (localRiesz alpha chi P))‖ <= C B pairWeight`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Vg_near (d : ℕ) (hd : 2 ≤ d) (k : ℕ) (alpha M : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ src : Euc d × Euc d → ℝ, ContDiff ℝ (k : WithTop ℕ∞) src →
      (∀ Y v : Euc d, 2 < ‖v‖ → src (Y, v) = 0) → ∀ Bs : ℝ, 0 ≤ Bs →
      (∀ i j : ℕ, i + j ≤ k → ∀ Y v : Euc d, ‖r26t8a_nest i j src Y v‖ ≤ Bs * jbracket Y ^ (2 * M)) →
      ∀ X z : Euc d, ‖z‖ ≤ 4 → ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Wg alpha src (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2) Yw.2) X z‖ ≤
          C * Bs * jbracket X ^ (2 * M) := by
  obtain ⟨Cn, hCn0, hCn⟩ := r26t8a_Wg_near d hd k alpha M halpha had hM
  refine ⟨2 ^ k * Cn, by positivity, ?_⟩
  intro src hsrc hSv Bs hBs hbd X z hz p q hpq
  have hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Wg alpha src Yw.1 Yw.2) :=
    r26t8a_Wg_contDiff d hd alpha halpha had src (hsrc.of_le (by exact_mod_cast hpq)) hSv
  have hsh := r26t8a_shear (-(1 / 2 : ℝ)) p q _ hΨ X z
  refine hsh.trans ?_
  have hX : X + (-(1 / 2 : ℝ)) • z = X - (1 / 2 : ℝ) • z := by rw [neg_smul, sub_eq_add_neg]
  rw [hX]
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  set T : ℝ := Cn * Bs * jbracket X ^ (2 * M) with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hterm : ∀ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
      ‖r26t8a_nest (p + t) (q - t) (fun Yw : Euc d × Euc d => r26t8a_Wg alpha src Yw.1 Yw.2)
        (X - (1 / 2 : ℝ) • z) z‖ ≤ (q.choose t : ℝ) * T := by
    intro t ht
    have htq : t ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    have h1 := hCn src hsrc hSv Bs hBs hbd X z hz (p + t) (q - t) (by omega)
    have hch : (0 : ℝ) ≤ q.choose t := Nat.cast_nonneg _
    have hhalf : |(-(1 / 2 : ℝ))| ^ t ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (by norm_num [abs_neg, abs_of_pos])
    calc (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
          ‖r26t8a_nest (p + t) (q - t) (fun Yw : Euc d × Euc d => r26t8a_Wg alpha src Yw.1 Yw.2)
            (X - (1 / 2 : ℝ) • z) z‖ ≤ (q.choose t : ℝ) * 1 * T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hhalf hch) h1 (norm_nonneg _) (by positivity)
      _ = (q.choose t : ℝ) * T := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ)) = 2 ^ q := by
    exact_mod_cast Nat.sum_range_choose q
  rw [hsum]
  calc (2 : ℝ) ^ q * T ≤ 2 ^ k * T :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hT0
    _ = 2 ^ k * Cn * Bs * jbracket X ^ (2 * M) := by rw [hT]; ring

end HRS.MS.R26T8A
