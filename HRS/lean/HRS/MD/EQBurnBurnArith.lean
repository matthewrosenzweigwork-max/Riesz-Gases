import HRS.MD.EQBurnBurnBase
import HRS.MD.EQ29Vocab

/-!
# EQ-BURN P4, part 7: the final arithmetic

`eqb_smooth_arith` and `eqb_wass_arith` turn the bounds of the three terms of `t25p_stage2` (initial term, remainder majorant, trace term) into the
two inequalities of `BurninConcl`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQBurnBurn

theorem eqb_smooth_arith {sd K e S0 Cr Ct b δ C : ℝ} {I0 B1 J : ℝ≥0∞}
    (hK : 0 ≤ K) (he : 0 ≤ e) (hS0 : 0 ≤ S0) (hCr : 0 ≤ Cr) (hCt : 0 ≤ Ct) (hδ : 0 ≤ δ) (hb0 : 0 ≤ b)
    (hI : I0 ≤ ENNReal.ofReal S0) (hB : B1 ≤ ENNReal.ofReal (Cr * Real.sqrt δ))
    (hJ : J ≤ ENNReal.ofReal (Ct * b)) (hb : b ≤ 2 * Real.sqrt δ)
    (hC1 : K * S0 ≤ C) (hC2 : Cr + K ^ 2 * Ct ≤ C)
    (h : ENNReal.ofReal sd ≤ ENNReal.ofReal (K * e) * I0 + B1 + ENNReal.ofReal (K ^ 2 / 2) * J) :
    sd ≤ C * (e + Real.sqrt δ) := by
  have hsq := Real.sqrt_nonneg δ
  have h1 : ENNReal.ofReal sd ≤ ENNReal.ofReal (K * e * S0 + Cr * Real.sqrt δ + K ^ 2 / 2 * (Ct * b)) := by
    refine h.trans ?_
    calc ENNReal.ofReal (K * e) * I0 + B1 + ENNReal.ofReal (K ^ 2 / 2) * J
        ≤ ENNReal.ofReal (K * e) * ENNReal.ofReal S0 + ENNReal.ofReal (Cr * Real.sqrt δ) +
          ENNReal.ofReal (K ^ 2 / 2) * ENNReal.ofReal (Ct * b) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hC0 : 0 ≤ C := (mul_nonneg hK hS0).trans hC1
  have h2 : K * e * S0 + Cr * Real.sqrt δ + K ^ 2 / 2 * (Ct * b) ≤ C * (e + Real.sqrt δ) := by
    have hKt : 0 ≤ K ^ 2 * Ct := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ K ^ 2 / 2 * Ct), mul_nonneg he (sub_nonneg.2 hC1),
      mul_nonneg hsq (sub_nonneg.2 hC2)]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h1.trans (ENNReal.ofReal_le_ofReal h2))

theorem eqb_wass_arith {W : ℝ≥0∞} {Q e S0 Rm Rt n δ C : ℝ} {A Bq Jh : ℝ≥0∞}
    (hQ : 0 ≤ Q) (he : 0 ≤ e) (hS0 : 0 ≤ S0) (hRm : 0 ≤ Rm) (hRt : 0 ≤ Rt) (hn : 0 ≤ n) (hδ : 0 ≤ δ)
    (hA : A ≤ ENNReal.ofReal S0) (hB : Bq ≤ ENNReal.ofReal (Rm * Real.sqrt δ))
    (hJ : Jh ≤ ENNReal.ofReal (Rt * (n + Real.sqrt δ)))
    (hC1 : Q * S0 ≤ C) (hC2 : Rm + Q * Rt ≤ C)
    (h : W ≤ ENNReal.ofReal (Q * e) * A + Bq + ENNReal.ofReal Q * Jh) :
    W ≤ ENNReal.ofReal (C * (e + n + Real.sqrt δ)) := by
  have hsq := Real.sqrt_nonneg δ
  refine h.trans ?_
  have h1 : ENNReal.ofReal (Q * e) * A + Bq + ENNReal.ofReal Q * Jh ≤
      ENNReal.ofReal (Q * e * S0 + Rm * Real.sqrt δ + Q * (Rt * (n + Real.sqrt δ))) := by
    calc ENNReal.ofReal (Q * e) * A + Bq + ENNReal.ofReal Q * Jh
        ≤ ENNReal.ofReal (Q * e) * ENNReal.ofReal S0 + ENNReal.ofReal (Rm * Real.sqrt δ) +
          ENNReal.ofReal Q * ENNReal.ofReal (Rt * (n + Real.sqrt δ)) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [mul_nonneg he (sub_nonneg.2 hC1), mul_nonneg hsq (sub_nonneg.2 hC2), mul_nonneg hn (sub_nonneg.2 hC2),
    mul_nonneg hn hRm, mul_nonneg hn hQ, mul_nonneg hRt hn, mul_nonneg (mul_nonneg hQ hRt) hn]

end HRS.MD.EQBurnBurn

end
