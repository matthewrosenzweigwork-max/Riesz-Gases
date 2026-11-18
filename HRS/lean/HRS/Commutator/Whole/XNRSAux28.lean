import HRS.Commutator.Whole.XNRSAux27

/-!
# Packet X-NRS, part 28: the Riesz-kernel bilinear form
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `|z|^{-q}` truncated to the ball of radius `R`. -/
def xkapR (d : ℕ) (q R : ℝ) : Euc d → ℝ :=
  (Metric.ball (0 : Euc d) R).indicator (fun z => ‖z‖ ^ (-q))

lemma xkapR_nonneg (q R : ℝ) (z : Euc d) : 0 ≤ xkapR d q R z := by
  unfold xkapR
  exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) _

lemma integrable_xkapR (hd : 1 ≤ d) {q : ℝ} (hq : q < d) (R : ℝ) : Integrable (xkapR d q R) := by
  unfold xkapR
  rw [integrable_indicator_iff measurableSet_ball]
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := q) (r := R)
    (by simpa using hd) (by simpa using hq) ?_ ?_
  · refine Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; simp
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma xpow_le_kapR {q : ℝ} (hq : 0 ≤ q) {R : ℝ} (hR : 0 < R) (z : Euc d) :
    ‖z‖ ^ (-q) ≤ xkapR d q R z + R ^ (-q) := by
  unfold xkapR
  by_cases hz : z ∈ Metric.ball (0 : Euc d) R
  · rw [Set.indicator_of_mem hz]
    have : 0 ≤ R ^ (-q) := Real.rpow_nonneg hR.le _
    linarith
  · rw [Set.indicator_of_notMem hz]
    have h1 : R ≤ ‖z‖ := by simpa using hz
    have : ‖z‖ ^ (-q) ≤ R ^ (-q) := Real.rpow_le_rpow_of_nonpos hR h1 (by linarith)
    linarith

/-- `N(R) = ∫_{B_R} |z|^{-q}`. -/
def xNR (d : ℕ) (q R : ℝ) : ℝ := ∫ z : Euc d, xkapR d q R z

lemma xNR_nonneg (q R : ℝ) : 0 ≤ xNR d q R := integral_nonneg fun z => xkapR_nonneg q R z

lemma xint_prod_conv {f g : Euc d → ℝ} (hf : Integrable f) (hg : Integrable g) :
    ∫ p : Euc d × Euc d, f p.2 * g (p.1 - p.2) ∂(volume.prod volume) = (∫ y, f y) * ∫ y, g y := by
  rw [integral_prod _ (xconv_int hf hg)]
  have := integral_convolution (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    (ContinuousLinearMap.mul ℝ ℝ) hf hg
  simpa [convolution_def] using this

/-- the absolute pair integral. -/
def xIa (s : ℝ) (f g : Euc d → ℝ) : ℝ :=
  ∫ p : Euc d × Euc d, ‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|) ∂(volume.prod volume)

lemma xIa_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f g : Euc d → ℝ}
    {φf φg : 𝓢(Euc d, ℂ)} (hf : ∀ x, φf x = (f x : ℂ)) (hg : ∀ x, φg x = (g x : ℂ)) :
    Integrable (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|)) (volume.prod volume) := by
  have hfa : ∀ x, ‖φf x‖ = |f x| := fun x => by rw [hf, Complex.norm_real, Real.norm_eq_abs]
  have hga : ∀ x, ‖φg x‖ = |g x| := fun x => by rw [hg, Complex.norm_real, Real.norm_eq_abs]
  have hw : Integrable (fun x => |f x|) := by
    have := (φf.integrable (μ := volume)).norm
    simpa only [hfa] using this
  have hwc : Continuous (fun x => |f x|) := by
    have : (fun x => |f x|) = fun x => ‖φf x‖ := funext fun x => (hfa x).symm
    rw [this]; exact φf.continuous.norm
  have := xint_kernel_prod hd hs0 hsd hw hwc φg
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only [hga]
  ring

lemma xIa_symm (s : ℝ) (f g : Euc d → ℝ) : xIa s f g = xIa s g f := by
  unfold xIa
  rw [← integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    (fun p : Euc d × Euc d => ‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|))]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]; ring

lemma xIa_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f g : Euc d → ℝ}
    {φf φg : 𝓢(Euc d, ℂ)} (hf : ∀ x, φf x = (f x : ℂ)) (hg : ∀ x, φg x = (g x : ℂ))
    {R : ℝ} (hR : 0 < R) {Mf : ℝ} (hMf : ∀ x, |f x| ≤ Mf) :
    xIa s f g ≤ xNR d s R * Mf * (∫ y, |g y|) + R ^ (-s) * (∫ y, |f y|) * ∫ y, |g y| := by
  have hfa : ∀ x, ‖φf x‖ = |f x| := fun x => by rw [hf, Complex.norm_real, Real.norm_eq_abs]
  have hga : ∀ x, ‖φg x‖ = |g x| := fun x => by rw [hg, Complex.norm_real, Real.norm_eq_abs]
  have hfi : Integrable (fun x => |f x|) := by
    have := (φf.integrable (μ := volume)).norm
    simpa only [hfa] using this
  have hgi : Integrable (fun x => |g x|) := by
    have := (φg.integrable (μ := volume)).norm
    simpa only [hga] using this
  have hF := xIa_int hd hs0 hsd hf hg
  have h1 : Integrable (fun p : Euc d × Euc d => |g p.2| * xkapR d s R (p.1 - p.2)) (volume.prod volume) :=
    xconv_int hgi (integrable_xkapR hd hsd R)
  have h2 : Integrable (fun p : Euc d × Euc d => |f p.1| * |g p.2|) (volume.prod volume) :=
    Integrable.mul_prod (f := fun x => |f x|) (g := fun y => |g y|) hfi hgi
  have hup : Integrable (fun p : Euc d × Euc d =>
      Mf * (|g p.2| * xkapR d s R (p.1 - p.2)) + R ^ (-s) * (|f p.1| * |g p.2|)) (volume.prod volume) :=
    (h1.const_mul Mf).add (h2.const_mul _)
  unfold xIa
  calc ∫ p : Euc d × Euc d, ‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|) ∂(volume.prod volume)
      ≤ ∫ p : Euc d × Euc d, (Mf * (|g p.2| * xkapR d s R (p.1 - p.2)) +
          R ^ (-s) * (|f p.1| * |g p.2|)) ∂(volume.prod volume) := by
        refine integral_mono hF hup fun p => ?_
        have hk := xpow_le_kapR (d := d) hs0 hR (p.1 - p.2)
        have h0 : 0 ≤ |f p.1| * |g p.2| := by positivity
        have hkk := xkapR_nonneg (d := d) s R (p.1 - p.2)
        calc ‖p.1 - p.2‖ ^ (-s) * (|f p.1| * |g p.2|)
            ≤ (xkapR d s R (p.1 - p.2) + R ^ (-s)) * (|f p.1| * |g p.2|) :=
              mul_le_mul_of_nonneg_right hk h0
          _ = xkapR d s R (p.1 - p.2) * (|f p.1| * |g p.2|) + R ^ (-s) * (|f p.1| * |g p.2|) := by ring
          _ ≤ Mf * (|g p.2| * xkapR d s R (p.1 - p.2)) + R ^ (-s) * (|f p.1| * |g p.2|) := by
              have := hMf p.1
              have hg0 := abs_nonneg (g p.2)
              have : xkapR d s R (p.1 - p.2) * (|f p.1| * |g p.2|) ≤
                  Mf * (|g p.2| * xkapR d s R (p.1 - p.2)) := by
                calc xkapR d s R (p.1 - p.2) * (|f p.1| * |g p.2|)
                    = |f p.1| * (|g p.2| * xkapR d s R (p.1 - p.2)) := by ring
                  _ ≤ Mf * (|g p.2| * xkapR d s R (p.1 - p.2)) :=
                    mul_le_mul_of_nonneg_right (hMf p.1) (mul_nonneg hg0 hkk)
              linarith
    _ = Mf * ((∫ y, |g y|) * xNR d s R) + R ^ (-s) * ((∫ y, |f y|) * ∫ y, |g y|) := by
        rw [integral_add (h1.const_mul Mf) (h2.const_mul _), integral_const_mul, integral_const_mul,
          xint_prod_conv hgi (integrable_xkapR hd hsd R)]
        rw [integral_prod_mul (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
          (fun x => |f x|) (fun y => |g y|)]
        rfl
    _ = _ := by ring

end HRS.Commutator.Whole.XNRS
