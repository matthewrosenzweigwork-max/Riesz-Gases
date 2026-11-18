import HRS.MS.SA12V3P

/-!
# S.A.12 C2 (SA12V3 worker), part Q: weight comparison between a periodic cell and its source cell

For `cz = c' + L k` (`L ≥ 1`, `k ∈ ℤ^d`), `‖c'‖ < 2 + L/3`, `‖ct - c'‖ ≤ D`:
`⟨cz⟩^{-(d+3)} ≤ Qw ⟨k⟩^{-(d+3)} ⟨ct⟩^{-(d+3)}`, `Qw` depending on `d, D` only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12v3_jb_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [norm_nonneg x]

theorem sa12v3_le_jb (x : Euc d) : 1 + ‖x‖ ≤ Real.sqrt 2 * jbracket x := by
  unfold jbracket
  rw [← Real.sqrt_mul (by norm_num)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

theorem sa12v3_jb_pos (x : Euc d) : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)

theorem sa12v3_weight_cmp (D : ℝ) (hD : 0 ≤ D) :
    ∃ Qw : ℝ, 0 < Qw ∧ ∀ L : ℝ, 1 ≤ L → ∀ (k : Fin d → ℤ) (cz ct c' : Euc d), cz = c' + L • latticePt k →
      ‖c'‖ < 2 + L / 3 → ‖ct - c'‖ ≤ D →
      jbracket cz ^ (-((d : ℝ) + 3)) ≤
        Qw * jbracket (latticePt k : Euc d) ^ (-((d : ℝ) + 3)) * jbracket ct ^ (-((d : ℝ) + 3)) := by
  set A : ℝ := 4 + D with hA
  set Q0 : ℝ := 42 * A + (1 + D) with hQ0
  set Qp : ℝ := Q0 * Real.sqrt 2 with hQp
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hQ0pos : 0 < Q0 := by positivity
  have hQppos : 0 < Qp := by positivity
  refine ⟨Qp ^ ((d : ℝ) + 3), Real.rpow_pos_of_pos hQppos _, fun L hL k cz ct c' hcz hc' hct => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  set n : ℝ := ‖(latticePt k : Euc d)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hct : 1 + ‖ct‖ ≤ A * L := by
    have : ‖ct‖ ≤ ‖c'‖ + D := by
      calc ‖ct‖ = ‖(ct - c') + c'‖ := by congr 1; abel
        _ ≤ ‖ct - c'‖ + ‖c'‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    rw [hA]; nlinarith
  have hcz_ge : L * n - ‖c'‖ ≤ ‖cz‖ := by
    have : L * n = ‖L • (latticePt k : Euc d)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL0]
    rw [this]
    have h2 := norm_sub_norm_le (L • (latticePt k : Euc d)) (-c')
    rw [sub_neg_eq_add, norm_neg] at h2
    rw [hcz, add_comm]; linarith
  have key : (1 + ‖ct‖) * (1 + n) ≤ Q0 * (1 + ‖cz‖) := by
    by_cases hk : n = 0
    · rw [hk]
      have : ‖cz‖ = ‖c'‖ := by
        have : (latticePt k : Euc d) = 0 := norm_eq_zero.1 hk
        rw [hcz, this]; simp
      have : 1 + ‖ct‖ ≤ (1 + D) * (1 + ‖cz‖) := by
        have h1 : ‖ct‖ ≤ ‖c'‖ + D := by
          calc ‖ct‖ = ‖(ct - c') + c'‖ := by congr 1; abel
            _ ≤ ‖ct - c'‖ + ‖c'‖ := norm_add_le _ _
            _ ≤ _ := by linarith
        nlinarith [norm_nonneg cz, norm_nonneg c']
      nlinarith [norm_nonneg cz, norm_nonneg ct]
    · have hn1 : 1 ≤ n := by
        -- a nonzero lattice point has norm at least one
        have hk0 : k ≠ 0 := by
          intro h; apply hk; rw [hn, h]; exact norm_eq_zero.2 (by ext i; simp [latticePt])
        obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
          by_contra hcon; push_neg at hcon; exact hk0 (funext hcon)
        have h1 : |(latticePt k : Euc d) i| ≤ n := by
          have := PiLp.norm_apply_le (latticePt k : Euc d) i
          simpa [Real.norm_eq_abs] using this
        have h2 : (1 : ℝ) ≤ |(latticePt k : Euc d) i| := by
          have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
          have h3 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast this
          simpa [latticePt] using h3
        linarith
      by_cases h6 : 6 ≤ L * n
      · have h1 : L * n / 3 ≤ ‖cz‖ := by nlinarith
        nlinarith [norm_nonneg ct, norm_nonneg cz]
      · push_neg at h6
        have hn6 : n < 6 := by nlinarith
        have hL6 : L < 6 := by nlinarith
        have h1 : 1 + ‖ct‖ ≤ A * 6 := by
          calc 1 + ‖ct‖ ≤ A * L := hct
            _ ≤ A * 6 := mul_le_mul_of_nonneg_left hL6.le (by rw [hA]; linarith)
        have : (1 + ‖ct‖) * (1 + n) ≤ 42 * A := by
          have hA0 : 0 ≤ A := by rw [hA]; linarith
          nlinarith [norm_nonneg ct]
        nlinarith [norm_nonneg cz]
  -- pass to the Japanese bracket
  have hb1 : jbracket ct * jbracket (latticePt k : Euc d) ≤ Qp * jbracket cz := by
    calc jbracket ct * jbracket (latticePt k : Euc d) ≤ (1 + ‖ct‖) * (1 + n) :=
          mul_le_mul (sa12v3_jb_le _) (sa12v3_jb_le _) (sa12v3_jb_pos _).le (by positivity)
      _ ≤ Q0 * (1 + ‖cz‖) := key
      _ ≤ Q0 * (Real.sqrt 2 * jbracket cz) := mul_le_mul_of_nonneg_left (sa12v3_le_jb _) hQ0pos.le
      _ = Qp * jbracket cz := by rw [hQp]; ring
  have hpp : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
  have hcpos : 0 < jbracket cz := sa12v3_jb_pos _
  have hbpos : 0 < jbracket (latticePt k : Euc d) := sa12v3_jb_pos _
  have htpos : 0 < jbracket ct := sa12v3_jb_pos _
  have h2 : (jbracket ct * jbracket (latticePt k : Euc d) / Qp) ≤ jbracket cz := by
    rw [div_le_iff₀ hQppos]; linarith
  have h3 : jbracket cz ^ (-((d : ℝ) + 3)) ≤ (jbracket ct * jbracket (latticePt k : Euc d) / Qp) ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h2 (by linarith)
  refine h3.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) hQppos.le, Real.mul_rpow htpos.le hbpos.le, Real.rpow_neg hQppos.le]
  field_simp

end HRS.MH.AdjointRd.Phase2SA12V3
