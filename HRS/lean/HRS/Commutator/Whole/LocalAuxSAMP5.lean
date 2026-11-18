import HRS.Commutator.Whole.LocalAuxFC
import HRS.Commutator.Whole.LocalAuxSAMP3

/-!
# `ψ` facts and `vhi_bounded` (packet CMX-SAMP, helper file 5)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- `ψ = ψ_1` as a Schwartz function. -/
def Om (d : ℕ) : SchwartzMap (Euc d) ℂ := cmxFB_Om (d := d) 1 one_pos

lemma Om_apply (x : Euc d) : Om d x = ((psiL 1 x : ℝ) : ℂ) := cmxFB_Om_apply one_pos x

lemma norm_Om (x : Euc d) : ‖Om d x‖ = |psiL 1 x| := by
  rw [Om_apply, Complex.norm_real, Real.norm_eq_abs]

lemma psi_continuous : Continuous (psiL 1 : Euc d → ℝ) := by
  have : Continuous fun x : Euc d => (Om d x).re := Complex.continuous_re.comp (Om d).continuous
  simpa [Om_apply] using this

lemma psi_measurable : Measurable (psiL 1 : Euc d → ℝ) := psi_continuous.measurable

lemma psi_integrable : Integrable (psiL 1 : Euc d → ℝ) := by
  have h2 : Integrable (fun x : Euc d => |psiL 1 x|) := by
    refine (((Om d).integrable (μ := (volume : Measure (Euc d)))).norm).congr
      (Eventually.of_forall fun x => ?_)
    simp [norm_Om]
  exact (integrable_norm_iff psi_continuous.aestronglyMeasurable).1
    (by simpa [Real.norm_eq_abs] using h2)

lemma psi_moment (k : ℕ) : Integrable (fun y : Euc d => ‖y‖ ^ k * |psiL 1 y|) := by
  refine ((Om d).integrable_pow_mul (volume : Measure (Euc d)) k).congr (Eventually.of_forall fun x => ?_)
  simp [norm_Om]

lemma psi_integral : ∫ y : Euc d, psiL 1 y = 1 := cmxFB_integral_psiL one_pos


lemma lip_norm_le {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (x y : Euc d) :
    ‖v x - v y‖ ≤ L * ‖x - y‖ := by
  have := hL.dist_le_mul x y
  rwa [dist_eq_norm, dist_eq_norm] at this

lemma lip_norm_growth {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (x : Euc d) :
    ‖v x‖ ≤ ‖v 0‖ + L * ‖x‖ := by
  have := lip_norm_le hL x 0
  rw [sub_zero] at this
  calc ‖v x‖ = ‖(v x - v 0) + v 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖v x - v 0‖ + ‖v 0‖ := norm_add_le _ _
    _ ≤ _ := by linarith

lemma psi_smul_integrable {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (x : Euc d) :
    Integrable (fun y => psiL 1 y • v (x - y)) := by
  have hb : Integrable (fun y : Euc d => (‖v x‖ + L * ‖y‖) * |psiL 1 y|) := by
    have h1 := (psi_moment (d := d) 0).const_mul ‖v x‖
    have h2 := (psi_moment (d := d) 1).const_mul (L : ℝ)
    refine (h1.add h2).congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, pow_zero, pow_one, one_mul]; ring
  refine hb.mono' ((psi_continuous.smul (hL.continuous.comp (continuous_const.sub
    continuous_id))).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  have := lip_norm_le hL (x - y) 0
  have h3 := lip_norm_growth hL (x - y)
  calc ‖v (x - y)‖ ≤ ‖v x‖ + ‖v (x - y) - v x‖ := by
        calc ‖v (x - y)‖ = ‖(v (x - y) - v x) + v x‖ := by rw [sub_add_cancel]
          _ ≤ _ := by rw [add_comm]; exact norm_add_le _ _
    _ ≤ ‖v x‖ + L * ‖(x - y) - x‖ := by gcongr; exact lip_norm_le hL _ _
    _ = ‖v x‖ + L * ‖y‖ := by rw [sub_sub_cancel_left, norm_neg]

lemma Pgt_eq {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (x : Euc d) :
    Pgt 1 v x = ∫ y : Euc d, psiL 1 y • (v x - v (x - y)) := by
  have h1 : ∫ y : Euc d, psiL 1 y • v x = v x := by
    rw [integral_smul_const, psi_integral, one_smul]
  have h2 : Integrable (fun y : Euc d => psiL 1 y • v x) := psi_integrable.smul_const _
  simp_rw [smul_sub]
  rw [integral_sub h2 (psi_smul_integrable hL x), h1]
  rfl


theorem vhi_bounded_core (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0), LipschitzWith L v →
      Continuous (Pgt 1 v) ∧
      (∀ x, Pgt 1 v x = ∫ y : Euc d, psiL 1 y • (v x - v (x - y))) ∧
      ∀ x, ‖Pgt 1 v x‖ ≤ C * L := by
  set M : ℝ := ∫ y : Euc d, ‖y‖ ^ 1 * |psiL 1 y| with hM
  have hM0 : 0 ≤ M := integral_nonneg fun y => by positivity
  refine ⟨M + 1, by positivity, fun v L hL => ⟨?_, fun x => Pgt_eq hL x, fun x => ?_⟩⟩
  · have hb : Integrable (fun y : Euc d => (L : ℝ) * (‖y‖ ^ 1 * |psiL 1 y|)) :=
      (psi_moment (d := d) 1).const_mul _
    have : Continuous fun x => ∫ y : Euc d, psiL 1 y • (v x - v (x - y)) := by
      refine continuous_of_dominated (bound := fun y => (L : ℝ) * (‖y‖ ^ 1 * |psiL 1 y|)) ?_ ?_ hb ?_
      · intro x
        exact (psi_continuous.smul (continuous_const.sub (hL.continuous.comp
          (continuous_const.sub continuous_id)))).aestronglyMeasurable
      · intro x
        refine Eventually.of_forall fun y => ?_
        rw [norm_smul, Real.norm_eq_abs, pow_one, mul_comm]
        calc ‖v x - v (x - y)‖ * |psiL 1 y| ≤ (L * ‖x - (x - y)‖) * |psiL 1 y| :=
              mul_le_mul_of_nonneg_right (lip_norm_le hL _ _) (abs_nonneg _)
          _ = _ := by rw [sub_sub_cancel]; ring
      · exact Eventually.of_forall fun y => by
          have := hL.continuous
          fun_prop
    have e : Pgt 1 v = fun x => ∫ y : Euc d, psiL 1 y • (v x - v (x - y)) :=
      funext fun x => Pgt_eq hL x
    rw [e]; exact this
  · have hb : Integrable (fun y : Euc d => (L : ℝ) * (‖y‖ ^ 1 * |psiL 1 y|)) :=
      (psi_moment (d := d) 1).const_mul _
    rw [Pgt_eq hL x]
    refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun y => ?_)).trans ?_
    · rw [norm_smul, Real.norm_eq_abs, pow_one, mul_comm]
      calc ‖v x - v (x - y)‖ * |psiL 1 y| ≤ (L * ‖x - (x - y)‖) * |psiL 1 y| :=
            mul_le_mul_of_nonneg_right (lip_norm_le hL _ _) (abs_nonneg _)
        _ = _ := by rw [sub_sub_cancel]; ring
    · rw [integral_const_mul, ← hM]
      have : (0 : ℝ) ≤ L := L.2
      nlinarith

end HRS.Commutator.Whole.SAMP1
