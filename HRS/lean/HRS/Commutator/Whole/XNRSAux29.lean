import HRS.Commutator.Whole.XNRSAux28

/-!
# Packet X-NRS, part 29: the commutator as a bilinear form
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xlip_continuous {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) : Continuous v := by
  have : LipschitzWith ⟨L, hL0⟩ v := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact hL x y
  exact this.continuous

lemma xkv_bound {s : ℝ} (hs0 : 0 ≤ s) {v : Euc d → Euc d} {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L)
    (x y : Euc d) :
    |commKer (kernGrad s) v x y| ≤ L * ‖x - y‖ ^ (-s) := by
  unfold commKer
  split_ifs with h
  · simp only [abs_zero]
    exact mul_nonneg hL0 (Real.rpow_nonneg (norm_nonneg _) _)
  · have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
    calc |inner ℝ (v x - v y) (kernGrad s (x - y))|
        ≤ ‖v x - v y‖ * ‖kernGrad s (x - y)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_inner_le_norm _ _
      _ ≤ (L * ‖x - y‖) * ‖x - y‖ ^ (-(s + 1)) :=
          mul_le_mul (hL x y) (HRS.Commutator.Whole.cmxFB_kernGrad_norm_le hs0 _)
            (norm_nonneg _) (mul_nonneg hL0 (norm_nonneg _))
      _ = L * ‖x - y‖ ^ (-s) := by
          have : ‖x - y‖ ^ (1 : ℝ) * ‖x - y‖ ^ (-(s + 1)) = ‖x - y‖ ^ (-s) := by
            rw [← Real.rpow_add hpos]
            congr 1; ring
          rw [Real.rpow_one] at this
          rw [mul_assoc, this]

/-- The bilinear form. -/
def xBil (s : ℝ) (v : Euc d → Euc d) (f g : Euc d → ℝ) : ℝ :=
  ∫ p : Euc d × Euc d, commKer (kernGrad s) v p.1 p.2 * (f p.1 * g p.2) ∂(volume.prod volume)

lemma xBil_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → Euc d} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : XLip v L) {f g : Euc d → ℝ} {φf φg : 𝓢(Euc d, ℂ)}
    (hf : ∀ x, φf x = (f x : ℂ)) (hg : ∀ x, φg x = (g x : ℂ)) :
    Integrable (fun p : Euc d × Euc d => commKer (kernGrad s) v p.1 p.2 * (f p.1 * g p.2))
      (volume.prod volume) := by
  have hI := xIa_int hd hs0 hsd hf hg
  have hfc : Continuous f := by
    have : f = fun x => (φf x).re := by funext x; rw [hf]; simp
    rw [this]; exact Complex.continuous_re.comp φf.continuous
  have hgc : Continuous g := by
    have : g = fun x => (φg x).re := by funext x; rw [hg]; simp
    rw [this]; exact Complex.continuous_re.comp φg.continuous
  refine (hI.const_mul L).mono' ?_ (Eventually.of_forall fun p => ?_)
  · have := (HRS.Commutator.Whole.cmxSA_commKer_measurable s (xlip_continuous hL0 hL).measurable)
    exact (this.mul ((hfc.measurable.comp measurable_fst).mul
      (hgc.measurable.comp measurable_snd))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |commKer (kernGrad s) v p.1 p.2| * (|f p.1| * |g p.2|)
        ≤ (L * ‖p.1 - p.2‖ ^ (-s)) * (|f p.1| * |g p.2|) :=
          mul_le_mul_of_nonneg_right (xkv_bound hs0 hL0 hL _ _) (by positivity)
      _ = L * (‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|)) := by ring

lemma xBil_abs_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → Euc d} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : XLip v L) {f g : Euc d → ℝ} {φf φg : 𝓢(Euc d, ℂ)}
    (hf : ∀ x, φf x = (f x : ℂ)) (hg : ∀ x, φg x = (g x : ℂ)) :
    |xBil s v f g| ≤ L * xIa s f g := by
  have hI := xIa_int hd hs0 hsd hf hg
  have hB := xBil_int hd hs0 hsd hL0 hL hf hg
  unfold xBil xIa
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono hB.abs (hI.const_mul L) fun p => ?_
  show |commKer (kernGrad s) v p.1 p.2 * (f p.1 * g p.2)| ≤ L * (‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|))
  rw [abs_mul, abs_mul]
  calc |commKer (kernGrad s) v p.1 p.2| * (|f p.1| * |g p.2|)
      ≤ (L * ‖p.1 - p.2‖ ^ (-s)) * (|f p.1| * |g p.2|) :=
        mul_le_mul_of_nonneg_right (xkv_bound hs0 hL0 hL _ _) (by positivity)
    _ = L * (‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|)) := by ring

lemma xCcomm_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → Euc d} {L : ℝ}
    (hL0 : 0 ≤ L) (hL : XLip v L) {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)}
    (ha : ∀ x, φ x = (a x : ℂ)) :
    CcommFun (kernGrad s) v a = xBil s v a a := by
  have hB := xBil_int hd hs0 hsd hL0 hL ha ha
  unfold xBil CcommFun
  rw [integral_prod _ hB]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only; ring

end HRS.Commutator.Whole.XNRS
