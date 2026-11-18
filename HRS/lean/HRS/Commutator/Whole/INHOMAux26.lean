import HRS.Commutator.Whole.INHOMAux25

/-!
# CMX-INHOM auxiliary 26: `L²` continuity of the commutator form
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- `W(z) = |z| |∇g_{>1}(z)|`. -/
def inhom_W (s : ℝ) (z : Euc d) : ℝ := ‖z‖ * ‖ghiForce s z‖

lemma inhom_W_props (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Measurable (inhom_W (d := d) s) ∧ Integrable (inhom_W (d := d) s) volume ∧
      (∀ z, 0 ≤ inhom_W (d := d) s z) ∧ (∀ z, inhom_W (d := d) s (-z) = inhom_W (d := d) s z) := by
  refine ⟨?_, ?_, fun z => by unfold inhom_W; positivity, fun z => ?_⟩
  · exact measurable_norm.mul (inhom_ghi_measurable hd hs0 hsd).norm
  · exact memLp_one_iff_integrable.1 (kernel_remainder_Lp hd hs0 hsd).1
  · unfold inhom_W
    rw [inhom_ghi_odd, norm_neg, norm_neg]

lemma inhom_commKer_ghi_bound {v : Euc d → Euc d} {L : ℝ≥0} (hL : LipschitzWith L v) (x y : Euc d) :
    |commKer (ghiForce s) v x y| ≤ L * inhom_W (d := d) s (x - y) := by
  rw [lowv_commKer_eq]
  unfold lowv_K inhom_W
  have h1 : ‖v x - v y‖ ≤ L * ‖x - y‖ := by simpa [dist_eq_norm] using hL.dist_le_mul x y
  calc |inner ℝ (v x - v y) (ghiForce s (x - y))| ≤ ‖v x - v y‖ * ‖ghiForce s (x - y)‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (L * ‖x - y‖) * ‖ghiForce s (x - y)‖ := by gcongr
    _ = _ := by ring

theorem inhom_L2_form (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {v : Euc d → Euc d}
    {L : ℝ≥0} (hL : LipschitzWith L v) {f g : Euc d → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x => f x ^ 2) volume) (hg2 : Integrable (fun x => g x ^ 2) volume)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : Euc d × Euc d => commKer (ghiForce s) v p.1 p.2 * f p.1 * g p.2)
        (volume.prod volume) ∧
      |∫ p : Euc d × Euc d, commKer (ghiForce s) v p.1 p.2 * f p.1 * g p.2 ∂(volume.prod volume)| ≤
        L * ((t * (∫ x, f x ^ 2) + t⁻¹ * (∫ x, g x ^ 2)) / 2 * ∫ z, inhom_W (d := d) s z) := by
  obtain ⟨hWm, hW, hWn, hWe⟩ := inhom_W_props hd hs0 hsd (d := d)
  obtain ⟨hS1, hS2⟩ := inhom_schur hWm hW hWn hWe hf hg hf2 hg2 ht
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hKm : Measurable fun p : Euc d × Euc d => commKer (ghiForce s) v p.1 p.2 := by
    have : (fun p : Euc d × Euc d => commKer (ghiForce s) v p.1 p.2) =
        fun p : Euc d × Euc d => inner ℝ (v p.1 - v p.2) (ghiForce s (p.1 - p.2)) := by
      funext p; rw [lowv_commKer_eq]; rfl
    rw [this]
    exact (((hL.continuous.measurable.comp measurable_fst).sub
      (hL.continuous.measurable.comp measurable_snd))).inner
      ((inhom_ghi_measurable hd hs0 hsd).comp (measurable_fst.sub measurable_snd))
  have hmeasf : AEStronglyMeasurable (fun p : Euc d × Euc d => f p.1) (volume.prod volume) :=
    hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hmeasg : AEStronglyMeasurable (fun p : Euc d × Euc d => g p.2) (volume.prod volume) :=
    hg.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hdom : Integrable (fun p : Euc d × Euc d =>
      L * (inhom_W (d := d) s (p.1 - p.2) * (|f p.1| * |g p.2|))) (volume.prod volume) :=
    hS1.const_mul _
  have hbd : ∀ p : Euc d × Euc d, ‖commKer (ghiForce s) v p.1 p.2 * f p.1 * g p.2‖ ≤
      L * (inhom_W (d := d) s (p.1 - p.2) * (|f p.1| * |g p.2|)) := by
    intro p
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |commKer (ghiForce s) v p.1 p.2| * |f p.1| * |g p.2|
        ≤ (L * inhom_W (d := d) s (p.1 - p.2)) * |f p.1| * |g p.2| := by
          gcongr; exact inhom_commKer_ghi_bound hL _ _
      _ = _ := by ring
  have hint : Integrable (fun p : Euc d × Euc d => commKer (ghiForce s) v p.1 p.2 * f p.1 * g p.2)
      (volume.prod volume) :=
    hdom.mono' ((hKm.aestronglyMeasurable.mul hmeasf).mul hmeasg) (Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖∫ p : Euc d × Euc d, commKer (ghiForce s) v p.1 p.2 * f p.1 * g p.2 ∂(volume.prod volume)‖
      ≤ ∫ p : Euc d × Euc d, L * (inhom_W (d := d) s (p.1 - p.2) * (|f p.1| * |g p.2|))
          ∂(volume.prod volume) := norm_integral_le_of_norm_le hdom (Eventually.of_forall hbd)
    _ = L * ∫ p : Euc d × Euc d, inhom_W (d := d) s (p.1 - p.2) * (|f p.1| * |g p.2|)
          ∂(volume.prod volume) := integral_const_mul _ _
    _ ≤ _ := by gcongr

end HRS.Commutator.Whole
