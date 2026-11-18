import HRS.Whole.Moving

/-!
# MOVTR auxiliary 1: the Riesz / logarithmic kernel, its smoothing and its gradient
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

/-- `σ = 1` for the logarithmic kernel, `σ = s` otherwise. -/
def movtr_sigma (s : ℝ) : ℝ := if s = 0 then 1 else s

/-- The smoothed kernel `g_ε`. -/
def movtr_gEps (d : ℕ) (s ε : ℝ) (z : Euc d) : ℝ :=
  if s = 0 then -(1 / 2) * Real.log (‖z‖ ^ 2 + ε ^ 2) else (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2)

lemma movtr_gEps_zero (d : ℕ) (s : ℝ) : movtr_gEps d s 0 = rieszKernel d s := by
  funext z
  unfold movtr_gEps rieszKernel
  by_cases hs : s = 0
  · simp [hs, Real.log_pow]
  · simp only [hs, ite_false]
    rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring

lemma movtr_hasFDerivAt_normSq_add (ε : ℝ) (z : Euc d) :
    HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2 + ε ^ 2) ((2 : ℝ) • innerSL ℝ z) z := by
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have e : ((2 : ℕ) • innerSL ℝ z : Euc d →L[ℝ] ℝ) = (2 : ℝ) • innerSL ℝ z := by
    rw [two_smul, two_smul]
  rw [e] at h
  exact h.add_const (ε ^ 2)

lemma movtr_gEps_hasFDerivAt (s ε : ℝ) (z : Euc d) (hu : 0 < ‖z‖ ^ 2 + ε ^ 2) :
    HasFDerivAt (movtr_gEps d s ε)
      ((-(movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1))) • innerSL ℝ z) z := by
  have hinner := movtr_hasFDerivAt_normSq_add ε z
  by_cases hs : s = 0
  · subst hs
    have h1 : HasDerivAt (fun u : ℝ => -(1 / 2) * Real.log u) (-(1 / 2) * (‖z‖ ^ 2 + ε ^ 2)⁻¹)
        (‖z‖ ^ 2 + ε ^ 2) := by
      exact (Real.hasDerivAt_log hu.ne').const_mul _
    have h2 := h1.comp_hasFDerivAt z hinner
    have : movtr_gEps d 0 ε = (fun u : ℝ => -(1 / 2) * Real.log u) ∘ (fun y : Euc d => ‖y‖ ^ 2 + ε ^ 2) := by
      funext y; simp [movtr_gEps]
    rw [this]
    convert h2 using 1
    simp only [movtr_sigma, ite_true, neg_zero, zero_div, zero_sub]
    rw [Real.rpow_neg_one, smul_smul]
    congr 1
    ring
  · have h1 : HasDerivAt (fun u : ℝ => u ^ (-s / 2)) ((-s / 2) * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1))
        (‖z‖ ^ 2 + ε ^ 2) := Real.hasDerivAt_rpow_const (Or.inl hu.ne')
    have h2 := h1.comp_hasFDerivAt z hinner
    have : movtr_gEps d s ε = (fun u : ℝ => u ^ (-s / 2)) ∘ (fun y : Euc d => ‖y‖ ^ 2 + ε ^ 2) := by
      funext y; simp [movtr_gEps, hs]
    rw [this]
    convert h2 using 1
    simp only [movtr_sigma, hs, ite_false, smul_smul]
    congr 1
    ring


/-- The exponent of the integrable majorant `‖z‖^{-s'}` of the kernel: `1/2` for `s = 0`. -/
def movtr_sp (s : ℝ) : ℝ := if s = 0 then 1 / 2 else s

lemma movtr_sp_pos {s : ℝ} (hs0 : 0 ≤ s) : 0 < movtr_sp s := by
  unfold movtr_sp
  split_ifs with h
  · norm_num
  · exact lt_of_le_of_ne hs0 (Ne.symm h)

lemma movtr_sp_lt {s : ℝ} (hsd : s < d) (hd : 1 ≤ d) : movtr_sp s < d := by
  unfold movtr_sp
  split_ifs with h
  · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  · exact hsd

/-- Pointwise bound of the smoothed kernel by an integrable majorant. -/
lemma movtr_gEps_abs_le {s : ℝ} (hs0 : 0 ≤ s) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {z : Euc d}
    (hz : z ≠ 0) :
    |movtr_gEps d s ε z| ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hpow : 0 ≤ ‖z‖ ^ (-movtr_sp s) := Real.rpow_nonneg hzpos.le _
  by_cases hs : s = 0
  · subst hs
    simp only [movtr_gEps, movtr_sp, ite_true]
    have hpow : 0 ≤ ‖z‖ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hzpos.le _
    have hu1 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ε]
    have hu2 : ‖z‖ ^ 2 + ε ^ 2 ≤ ‖z‖ ^ 2 + 1 := by nlinarith [sq_nonneg ε]
    by_cases h1 : 1 ≤ ‖z‖
    · have hlog0 : 0 ≤ Real.log (‖z‖ ^ 2 + ε ^ 2) :=
        Real.log_nonneg (by nlinarith)
      have hlog1 : Real.log (‖z‖ ^ 2 + ε ^ 2) ≤ 2 * ‖z‖ := by
        have h2 : ‖z‖ ^ 2 + ε ^ 2 ≤ 2 * ‖z‖ ^ 2 := by nlinarith
        calc Real.log (‖z‖ ^ 2 + ε ^ 2) ≤ Real.log (2 * ‖z‖ ^ 2) :=
              Real.log_le_log hu h2
          _ = Real.log 2 + 2 * Real.log ‖z‖ := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
          _ ≤ 1 + 2 * (‖z‖ - 1) + 1 := by
              have := Real.log_le_sub_one_of_pos hzpos
              have h2 : Real.log 2 < 1 := by
                have := Real.log_two_lt_d9; linarith
              linarith
          _ = 2 * ‖z‖ := by ring
      rw [abs_le]
      constructor <;> nlinarith
    · push Not at h1
      have hlog1 : Real.log (‖z‖ ^ 2 + ε ^ 2) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos hu
        nlinarith
      have hlog2 : 2 * Real.log ‖z‖ ≤ Real.log (‖z‖ ^ 2 + ε ^ 2) := by
        have h3 : Real.log (‖z‖ ^ 2) = 2 * Real.log ‖z‖ := by
          rw [Real.log_pow]; push_cast; ring
        rw [← h3]
        exact Real.log_le_log (by positivity) hu1
      have hlog3 : -Real.log ‖z‖ ≤ 2 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
        have := Real.log_le_rpow_div (inv_nonneg.mpr hzpos.le) (show (0:ℝ) < 1 / 2 by norm_num)
        rw [Real.log_inv, Real.inv_rpow hzpos.le, ← Real.rpow_neg hzpos.le] at this
        linarith
      rw [abs_le]
      constructor <;> nlinarith [hzpos]
  · simp only [movtr_gEps, movtr_sp, hs, ite_false]
    have h0 : 0 ≤ (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) := Real.rpow_nonneg hu.le _
    rw [abs_of_nonneg h0]
    have hle : (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2) ≤ (‖z‖ ^ 2) ^ (-s / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
    have h2 : (‖z‖ ^ 2) ^ (-s / 2) = ‖z‖ ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
      congr 1
      push_cast
      ring
    rw [h2] at hle
    have : ‖z‖ ^ (-s) = ‖z‖ ^ (-movtr_sp s) := by simp [movtr_sp, hs]
    simp only [movtr_sp, hs, ite_false] at hpow
    nlinarith [norm_nonneg z]

/-- `‖z‖^α e^{-c‖z‖²}` is integrable for `α > -d`. -/
lemma movtr_integrable_rpow_gauss (hd : 1 ≤ d) {α c : ℝ} (hα : -(d : ℝ) < α) (hc : 0 < c) :
    Integrable (fun z : Euc d => ‖z‖ ^ α * Real.exp (-c * ‖z‖ ^ 2)) := by
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp [finrank_euclideanSpace_fin]; omega
  have := (integrable_fun_norm_addHaar (volume : Measure (Euc d))
    (f := fun r : ℝ => r ^ α * Real.exp (-c * r ^ 2))).mpr
  apply this
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  have h := integrableOn_rpow_mul_exp_neg_mul_sq hc (s := (d : ℝ) - 1 + α) (by linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro y hy
  simp only
  have hy' : (0 : ℝ) < y := hy
  rw [Real.rpow_add hy', show ((d : ℝ) - 1) = ((d - 1 : ℕ) : ℝ) by
    rw [Nat.cast_sub hd]; simp, Real.rpow_natCast]
  ring

end HRS.Whole
