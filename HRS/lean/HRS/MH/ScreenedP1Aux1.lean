import HRS.MH.ScreenedDefs

/-!
# Helpers for packets P1 (`screened_pairing_lt`) and S5b (`gag_product`) of `B:lem:screened` (S.B.4).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- `∫⁻ (1+‖z‖)^{-q} < ∞` for `q > d`. -/
lemma p1_one_add_norm_lintegral_lt_top {q : ℝ} (hq : (d : ℝ) < q) :
    ∫⁻ z : Euc d, ENNReal.ofReal ((1 + ‖z‖) ^ (-q)) < ⊤ := by
  have hfin : (Module.finrank ℝ (Euc d) : ℝ) < q := by
    rw [finrank_euclideanSpace_fin]; exact hq
  exact (integrable_one_add_norm (μ := (volume : Measure (Euc d))) hfin).lintegral_lt_top

/-- Tail integral: `∫⁻_{|z|>1} |z|^{-t} < ∞` for `t > d`. -/
lemma p1_tail_lintegral_lt_top {t : ℝ} (ht : (d : ℝ) < t) :
    ∫⁻ z in (Metric.closedBall (0 : Euc d) 1)ᶜ, ENNReal.ofReal (‖z‖ ^ (-t)) < ⊤ := by
  have hpt : ∀ z ∈ (Metric.closedBall (0 : Euc d) 1)ᶜ,
      ENNReal.ofReal (‖z‖ ^ (-t)) ≤ ENNReal.ofReal (2 ^ t) * ENNReal.ofReal ((1 + ‖z‖) ^ (-t)) := by
    intro z hz
    have h1 : 1 < ‖z‖ := by
      rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
      exact hz
    have hz0 : 0 < ‖z‖ := by linarith
    have ht0 : (0 : ℝ) ≤ t := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h2 : (2 * ‖z‖) ^ (-t) ≤ (1 + ‖z‖) ^ (-t) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h2t : (2 : ℝ) ^ t * (2 : ℝ) ^ (-t) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have h3 : ‖z‖ ^ (-t) = 2 ^ t * (2 * ‖z‖) ^ (-t) := by
      rw [Real.mul_rpow (by norm_num) hz0.le, ← mul_assoc, h2t, one_mul]
    calc ENNReal.ofReal (‖z‖ ^ (-t)) = ENNReal.ofReal (2 ^ t * (2 * ‖z‖) ^ (-t)) := by rw [← h3]
      _ ≤ ENNReal.ofReal (2 ^ t * (1 + ‖z‖) ^ (-t)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = ENNReal.ofReal (2 ^ t) * ENNReal.ofReal ((1 + ‖z‖) ^ (-t)) :=
          ENNReal.ofReal_mul (by positivity)
  calc ∫⁻ z in (Metric.closedBall (0 : Euc d) 1)ᶜ, ENNReal.ofReal (‖z‖ ^ (-t))
      ≤ ∫⁻ z in (Metric.closedBall (0 : Euc d) 1)ᶜ,
          ENNReal.ofReal (2 ^ t) * ENNReal.ofReal ((1 + ‖z‖) ^ (-t)) :=
        setLIntegral_mono' Metric.isClosed_closedBall.measurableSet.compl hpt
    _ ≤ ∫⁻ z : Euc d, ENNReal.ofReal (2 ^ t) * ENNReal.ofReal ((1 + ‖z‖) ^ (-t)) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 ^ t) * ∫⁻ z : Euc d, ENNReal.ofReal ((1 + ‖z‖) ^ (-t)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (p1_one_add_norm_lintegral_lt_top ht)

lemma p1_one_le_jbracket (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [sq_nonneg ‖x‖]

/-- Japanese bracket integrability: `∫⁻ ⟨x⟩^{-q} < ∞` for `q > d`. -/
lemma p1_jb_rpow_lintegral_lt_top {q : ℝ} (hq : (d : ℝ) < q) :
    ∫⁻ x : Euc d, ENNReal.ofReal (jbracket x ^ (-q)) < ⊤ := by
  have hpt : ∀ x : Euc d,
      ENNReal.ofReal (jbracket x ^ (-q)) ≤ ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((1 + ‖x‖) ^ (-q)) := by
    intro x
    have hjb : (1 + ‖x‖) / 2 ≤ jbracket x := by
      unfold jbracket
      rw [Real.le_sqrt (by positivity) (by positivity)]
      nlinarith [sq_nonneg (‖x‖ - 1 / 3)]
    have hpos : 0 < (1 + ‖x‖) / 2 := by positivity
    have hq0 : (0 : ℝ) ≤ q := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have h2 : jbracket x ^ (-q) ≤ ((1 + ‖x‖) / 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hpos hjb (by linarith)
    have h3 : ((1 + ‖x‖) / 2) ^ (-q) = 2 ^ q * (1 + ‖x‖) ^ (-q) := by
      rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_inv_eq_mul, mul_comm]
    calc ENNReal.ofReal (jbracket x ^ (-q)) ≤ ENNReal.ofReal (2 ^ q * (1 + ‖x‖) ^ (-q)) := by
          rw [← h3]; exact ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((1 + ‖x‖) ^ (-q)) :=
          ENNReal.ofReal_mul (by positivity)
  calc ∫⁻ x : Euc d, ENNReal.ofReal (jbracket x ^ (-q))
      ≤ ∫⁻ x : Euc d, ENNReal.ofReal (2 ^ q) * ENNReal.ofReal ((1 + ‖x‖) ^ (-q)) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ q) * ∫⁻ x : Euc d, ENNReal.ofReal ((1 + ‖x‖) ^ (-q)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (p1_one_add_norm_lintegral_lt_top hq)

/-- `(a+b)² ≤ 2a² + 2b²` in `ℝ≥0∞`. -/
lemma p1_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  norm_num at h
  simpa [mul_add] using h

/-- Changing the first argument of an `IsGradKernelRep` on a null set keeps the representation. -/
lemma p1_gkRep_congr {s : ℝ} {i : Fin d} {v v' w : Euc d → ℝ} (h : IsGradKernelRep d s i v w)
    (hv : v =ᵐ[volume] v') : IsGradKernelRep d s i v' w := by
  intro φ
  obtain ⟨h1, h2, h3⟩ := h φ
  refine ⟨h1, h2.congr ?_, ?_⟩
  · filter_upwards [hv] with y hy
    simp only [hy]
  · rw [h3]
    congr 1
    exact integral_congr_ae (hv.mono fun y hy => by simp only [hy])

end HRS.MH.Screened
