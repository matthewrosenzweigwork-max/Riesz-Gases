import HRS.MS.R26T8AP21h

/-!
# S8.2 local Newton layer, packet T8A.P21 (part i): nested jets of `Q`
Small `z`: `|nest p q Q| <= 2 A (q+1)^4 |z|^(4-q)` (integral form of `Q` + nested jets of `u_4`); all `z`: `|nest p q Q| <= 3 A (q+1)^2 (1+|z|)^2`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Q_eq_u (f : Euc d → ℝ) (X z : Euc d) :
    r26t8a_Q f X z = r26t8a_u f X z 1 (1 / 2) - r26t8a_u f X z 1 (-1 / 2) - r26t8a_u f X z 2 0 := by
  have e1 : (X - (1 / 2 : ℝ) • z) = X + (-1 / 2 : ℝ) • z := by module
  unfold r26t8a_Q
  rw [r26t8a_u_one, r26t8a_u_one, r26t8a_u_two_zero, e1]

theorem r26t8a_u_param_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) {τ : ℝ → ℝ}
    (hτ : ContDiff ℝ ∞ τ) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun tYw : ℝ × (Euc d × Euc d) => r26t8a_u f tYw.2.1 tYw.2.2 (0 + m) (τ tYw.1)) := by
  have h0 := r26t8a_u_joint_contDiff hf m 0 N
  have hF : ContDiff ℝ (N : WithTop ℕ∞) (fun tYw : ℝ × (Euc d × Euc d) => (tYw.2.1 + (τ tYw.1) • tYw.2.2, tYw.2.2)) :=
    (((contDiff_snd.fst).add (((hτ.comp contDiff_fst).of_le (by exact_mod_cast le_top)).smul
      (contDiff_snd.snd))).prodMk (contDiff_snd.snd))
  have := h0.comp hF
  convert this using 2 with tYw
  simp [r26t8a_u]

theorem r26t8a_nest_Q_small {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {A : ℝ}
    (hA : ∀ j, 1 ≤ j → j ≤ k + 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi)
    (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) (hz : ‖z‖ ≤ 1) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) X z‖ ≤
      2 * A * ((q : ℝ) + 1) ^ 4 * ‖z‖ ^ (4 - q) := by
  set Θ : ℝ → Euc d × Euc d → ℝ := fun t Yw => (1 / 16 * (1 - t) ^ 2) *
    (r26t8a_u f Yw.1 Yw.2 (0 + 4) (t / 2) + r26t8a_u f Yw.1 Yw.2 (0 + 4) (-t / 2)) with hΘ
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => t / 2) := contDiff_id.div_const 2
  have h3 : ContDiff ℝ ∞ (fun t : ℝ => -t / 2) := (contDiff_id.neg).div_const 2
  have hΘd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun tYw : ℝ × (Euc d × Euc d) => Θ tYw.1 tYw.2) :=
    (((contDiff_const.mul ((contDiff_const.sub contDiff_fst).pow 2)).of_le (by exact_mod_cast le_top))).mul
      ((r26t8a_u_param_contDiff hf 4 h2 (p + q)).add (r26t8a_u_param_contDiff hf 4 h3 (p + q)))
  have hQ : (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) = fun Yw => ∫ t in (0 : ℝ)..1, Θ t Yw := by
    funext Yw
    rw [r26t8a_Q_integral hf, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [hΘ]
    rw [show (4 : ℕ) = 0 + 4 from rfl]
    ring
  rw [hQ, r26t8a_nest_integral hchi hΘd X z]
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1 le_rfl (by omega) 0)
  have hbd : ∀ t ∈ Set.uIoc (0 : ℝ) 1, ‖r26t8a_nest p q (Θ t) X z‖ ≤ 2 * A * ((q : ℝ) + 1) ^ 4 * ‖z‖ ^ (4 - q) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hS1 := r26t8a_u_joint_contDiff hf 4 (t / 2) (p + q)
    have hS2 := r26t8a_u_joint_contDiff hf 4 (-t / 2) (p + q)
    set L : ℝ →L[ℝ] ℝ := (1 / 16 * (1 - t) ^ 2) • ContinuousLinearMap.id ℝ ℝ with hL
    have hLn : ‖L‖ ≤ 1 := by
      refine (norm_smul _ _).trans_le ?_
      have h0 : 0 ≤ 1 - t := by linarith [ht.2]
      have h1 : 1 - t ≤ 1 := by linarith [ht.1]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc 1 / 16 * (1 - t) ^ 2 * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 / 16 * (1 - t) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (by positivity)
        _ ≤ 1 := by nlinarith
    have hΘt : Θ t = fun Yw => L (r26t8a_u f Yw.1 Yw.2 (0 + 4) (t / 2) + r26t8a_u f Yw.1 Yw.2 (0 + 4) (-t / 2)) := by
      funext Yw; simp [hΘ, hL]
    rw [hΘt]
    refine (r26t8a_nest_clm L hLn p q _ X z (hS1.add hS2)).trans ?_
    rw [r26t8a_nest_add p q z X hS1 hS2]
    refine (norm_add_le _ _).trans ?_
    have b1 := r26t8a_nest_u_small hf hA 4 (by norm_num) le_rfl (t / 2) (by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; have := abs_of_nonneg ht.1.le; rw [this]; linarith [ht.2]) p q hpq X z hz
    have b2 := r26t8a_nest_u_small hf hA 4 (by norm_num) le_rfl (-t / 2) (by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; have := abs_of_nonneg ht.1.le; rw [this]; linarith [ht.2]) p q hpq X z hz
    linarith
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) hbd
  simpa using this

end HRS.MS.R26T8A
