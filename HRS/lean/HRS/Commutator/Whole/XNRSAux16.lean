import HRS.Commutator.Whole.XNRSAux15
import HRS.Commutator.Whole.ApproxAux
import HRS.Commutator.Whole.LocalAuxFC2

/-!
# Packet X-NRS, part 16: `𝒞_g(v,a) = 2 ∫ a ⟨v, ∇g * a⟩`

Absolute integrability of the commutator kernel against a Schwartz density and the symmetrisation.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `|z|^{-q}` truncated to the unit ball. -/
def xkap (d : ℕ) (q : ℝ) : Euc d → ℝ := (Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-q))

lemma integrable_xkap (hd : 1 ≤ d) {q : ℝ} (hq : q < d) : Integrable (xkap d q) := by
  unfold xkap
  rw [integrable_indicator_iff measurableSet_ball]
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := q) (r := 1)
    (by simpa using hd) (by simpa using hq) ?_ ?_
  · refine Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; simp
  · exact (measurable_norm.pow_const _).aestronglyMeasurable

lemma xpow_le_kap {q : ℝ} (hq : 0 ≤ q) (z : Euc d) : ‖z‖ ^ (-q) ≤ xkap d q z + 1 := by
  unfold xkap
  by_cases hz : z ∈ Metric.ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hz]; linarith
  · rw [Set.indicator_of_notMem hz]
    have : 1 ≤ ‖z‖ := by simpa using hz
    have : ‖z‖ ^ (-q) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos this (by linarith)
    linarith

/-- Product integrability of `w(x) |φ(y)| |x-y|^{-q}`. -/
lemma xint_kernel_prod (hd : 1 ≤ d) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < d) {w : Euc d → ℝ}
    (hw : Integrable w) (hwm : Continuous w) (φ : 𝓢(Euc d, ℂ)) :
    Integrable (fun p : Euc d × Euc d => w p.1 * ‖φ p.2‖ * ‖p.1 - p.2‖ ^ (-q)) (volume.prod volume) := by
  obtain ⟨M, hM0, hM⟩ := xhbdd φ
  have h1 := xint_xy1 (a := fun x => |w x| * M) (G := xkap d q) (hw.abs.mul_const M) (integrable_xkap hd hq)
  have h2 : Integrable (fun p : Euc d × Euc d => |w p.1| * ‖φ p.2‖) (volume.prod volume) :=
    Integrable.mul_prod (f := fun x => |w x|) (g := fun y => ‖φ y‖) hw.abs φ.integrable.norm
  refine (h1.add h2).mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Measurable (fun p : Euc d × Euc d => w p.1 * ‖φ p.2‖ * ‖p.1 - p.2‖ ^ (-q)) := by
      refine ((hwm.measurable.comp measurable_fst).mul
        (φ.continuous.norm.measurable.comp measurable_snd)).mul ?_
      exact (measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _
    exact this.aestronglyMeasurable
  · show ‖w p.1 * ‖φ p.2‖ * ‖p.1 - p.2‖ ^ (-q)‖ ≤ |w p.1| * M * xkap d q (p.1 - p.2) + |w p.1| * ‖φ p.2‖
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have hk := xpow_le_kap (d := d) hq0 (p.1 - p.2)
    have hφ0 := norm_nonneg (φ p.2)
    have hw0 := abs_nonneg (w p.1)
    have hk0 : 0 ≤ xkap d q (p.1 - p.2) := by
      unfold xkap; exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) _
    calc |w p.1| * ‖φ p.2‖ * ‖p.1 - p.2‖ ^ (-q) ≤ |w p.1| * ‖φ p.2‖ * (xkap d q (p.1 - p.2) + 1) :=
          mul_le_mul_of_nonneg_left hk (mul_nonneg hw0 hφ0)
      _ = |w p.1| * ‖φ p.2‖ * xkap d q (p.1 - p.2) + |w p.1| * ‖φ p.2‖ := by ring
      _ ≤ |w p.1| * M * xkap d q (p.1 - p.2) + |w p.1| * ‖φ p.2‖ := by
          have := hM p.2
          have : |w p.1| * ‖φ p.2‖ * xkap d q (p.1 - p.2) ≤ |w p.1| * M * xkap d q (p.1 - p.2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM p.2) hw0) hk0
          linarith


lemma xint_kernel_y (hd : 1 ≤ d) {q : ℝ} (hq0 : 0 ≤ q) (hq : q < d) (φ : 𝓢(Euc d, ℂ)) (x : Euc d) :
    Integrable (fun y : Euc d => ‖x - y‖ ^ (-q) * ‖φ y‖) := by
  obtain ⟨M, hM0, hM⟩ := xhbdd φ
  have h1 : Integrable (fun y : Euc d => xkap d q (x - y)) :=
    (integrable_xkap hd hq).comp_sub_left x
  have h2 := (h1.const_mul M).add φ.integrable.norm
  refine h2.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).mul
      φ.continuous.norm.measurable |>.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    have hk := xpow_le_kap (d := d) hq0 (x - y)
    have hk0 : 0 ≤ xkap d q (x - y) := by
      unfold xkap; exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) _
    calc ‖x - y‖ ^ (-q) * ‖φ y‖ ≤ (xkap d q (x - y) + 1) * ‖φ y‖ :=
          mul_le_mul_of_nonneg_right hk (norm_nonneg _)
      _ = xkap d q (x - y) * ‖φ y‖ + ‖φ y‖ := by ring
      _ ≤ M * xkap d q (x - y) + ‖φ y‖ := by
          have := mul_le_mul_of_nonneg_left (hM y) hk0
          linarith


lemma xint_norm_lin (φ : 𝓢(Euc d, ℂ)) (a₀ L : ℝ) :
    Integrable (fun x : Euc d => (a₀ + L * ‖x‖) * ‖φ x‖) := by
  have h1 : Integrable (fun x : Euc d => a₀ * ‖φ x‖ + L * (‖x‖ ^ 1 * ‖φ x‖)) :=
    (φ.integrable.norm.const_mul a₀).add ((φ.integrable_pow_mul volume 1).const_mul L)
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only; ring

/-- `F₁(x,y) = ⟨v(x), ∇g(x-y)⟩ a(x) a(y)`. -/
def xF1 (v : Euc d → Euc d) (s : ℝ) (a : Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  inner ℝ (v p.1) (kernGrad s (p.1 - p.2)) * a p.1 * a p.2

/-- `F₂(x,y) = ⟨v(y), ∇g(x-y)⟩ a(x) a(y)`. -/
def xF2 (v : Euc d → Euc d) (s : ℝ) (a : Euc d → ℝ) (p : Euc d × Euc d) : ℝ :=
  inner ℝ (v p.2) (kernGrad s (p.1 - p.2)) * a p.1 * a p.2

lemma xF2_swap (v : Euc d → Euc d) (s : ℝ) (a : Euc d → ℝ) (p : Euc d × Euc d) :
    xF1 v s a p.swap = -xF2 v s a p := by
  unfold xF1 xF2
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [← neg_sub, HRS.Commutator.Whole.cmxFB_kernGrad_neg, inner_neg_right]
  ring

lemma xF1_int (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {v : Euc d → Euc d}
    (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) (a : Euc d → ℝ) (φ : 𝓢(Euc d, ℂ))
    (ha : ∀ x, φ x = (a x : ℂ)) :
    Integrable (xF1 v s a) (volume.prod volume) := by
  have hd1 : 1 ≤ d := by omega
  have haφ : ∀ x, ‖φ x‖ = |a x| := fun x => by rw [ha, Complex.norm_real, Real.norm_eq_abs]
  have hac : Continuous a := by
    have : a = fun x => (φ x).re := by funext x; rw [ha]; simp
    rw [this]; exact Complex.continuous_re.comp φ.continuous
  have hvc : Continuous v := by
    have h1 : Continuous (fun x => (v x).ofLp) := continuous_pi fun c => xtvf_continuous hv c
    have h2 := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp h1
    have h3 : ((WithLp.toLp 2 : (Fin d → ℝ) → Euc d) ∘ fun x => (v x).ofLp) = v := by
      funext x; simp
    rw [h3] at h2; exact h2
  have hw := xint_norm_lin φ ‖v 0‖ L
  have hb := xint_kernel_prod hd1 (q := s + 1) (by linarith) (by linarith) hw
    ((continuous_const.add (continuous_const.mul continuous_norm)).mul φ.continuous.norm) φ
  refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have : Measurable (xF1 v s a) := by
      unfold xF1
      refine (((hvc.measurable.comp measurable_fst).inner
        ((HRS.Commutator.Whole.cmxSA_kernGrad_measurable s).comp
          (measurable_fst.sub measurable_snd))).mul (hac.measurable.comp measurable_fst)).mul
        (hac.measurable.comp measurable_snd)
    exact this.aestronglyMeasurable
  · show ‖xF1 v s a p‖ ≤ (‖v 0‖ + L * ‖p.1‖) * ‖φ p.1‖ * ‖φ p.2‖ * ‖p.1 - p.2‖ ^ (-(s + 1))
    unfold xF1
    rw [norm_mul, norm_mul]
    have e1 : ‖a p.1‖ = ‖φ p.1‖ := by rw [haφ, Real.norm_eq_abs]
    have e2 : ‖a p.2‖ = ‖φ p.2‖ := by rw [haφ, Real.norm_eq_abs]
    rw [e1, e2]
    have hi : ‖inner ℝ (v p.1) (kernGrad s (p.1 - p.2))‖ ≤
        (‖v 0‖ + L * ‖p.1‖) * ‖p.1 - p.2‖ ^ (-(s + 1)) := by
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul (xv_growth hL p.1) (HRS.Commutator.Whole.cmxFB_kernGrad_norm_le hs0 _)
        (norm_nonneg _) (by positivity)
    have h1 := norm_nonneg (φ p.1)
    have h2 := norm_nonneg (φ p.2)
    calc ‖inner ℝ (v p.1) (kernGrad s (p.1 - p.2))‖ * ‖φ p.1‖ * ‖φ p.2‖
        ≤ ((‖v 0‖ + L * ‖p.1‖) * ‖p.1 - p.2‖ ^ (-(s + 1))) * ‖φ p.1‖ * ‖φ p.2‖ := by gcongr
      _ = _ := by ring


lemma xkern_comp_int (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (a : Euc d → ℝ)
    (φ : 𝓢(Euc d, ℂ)) (ha : ∀ x, φ x = (a x : ℂ)) (x : Euc d) (i : Fin d) :
    Integrable (fun y => kernGrad s (x - y) i * a y) := by
  have hd1 : 1 ≤ d := by omega
  have haφ : ∀ x, ‖φ x‖ = |a x| := fun x => by rw [ha, Complex.norm_real, Real.norm_eq_abs]
  have h := xint_kernel_y hd1 (q := s + 1) (by linarith) (by linarith) φ x
  refine h.mono' ?_ (Eventually.of_forall fun y => ?_)
  · have hac : Continuous a := by
      have : a = fun x => (φ x).re := by funext x; rw [ha]; simp
      rw [this]; exact Complex.continuous_re.comp φ.continuous
    have hm : Measurable (fun y => kernGrad s (x - y) i) :=
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable).comp
        ((HRS.Commutator.Whole.cmxSA_kernGrad_measurable s).comp
          (measurable_const.sub measurable_id))
    exact (hm.mul hac.measurable).aestronglyMeasurable
  · rw [norm_mul, haφ y, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have h1 : |kernGrad s (x - y) i| ≤ ‖kernGrad s (x - y)‖ := by
      have := PiLp.norm_apply_le (kernGrad s (x - y)) i
      simpa [Real.norm_eq_abs] using this
    exact h1.trans (HRS.Commutator.Whole.cmxFB_kernGrad_norm_le hs0 _)

theorem xB_real (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {v : Euc d → Euc d}
    (hv : XTVF v) {L : ℝ} (hL0 : 0 ≤ L) (hL : XLip v L) (a : Euc d → ℝ) (φ : 𝓢(Euc d, ℂ))
    (ha : ∀ x, φ x = (a x : ℂ)) :
    CcommFun (kernGrad s) v a =
      2 * ∫ x, a x * ∑ i, v x i * ∫ y, kernGrad s (x - y) i * a y := by
  have hF1 := xF1_int hd hs0 hsd hv hL0 hL a φ ha
  have hF2 : Integrable (xF2 v s a) (volume.prod volume) := by
    have h1 := hF1.swap
    have h2 : (xF1 v s a ∘ Prod.swap) = fun p => -xF2 v s a p := by
      funext p; exact xF2_swap v s a p
    rw [h2] at h1
    simpa using h1.neg
  have e1 : CcommFun (kernGrad s) v a = ∫ p : Euc d × Euc d, (xF1 v s a p - xF2 v s a p) := by
    unfold CcommFun
    have := (integral_prod (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      (fun p : Euc d × Euc d => xF1 v s a p - xF2 v s a p) (hF1.sub hF2))
    refine Eq.trans ?_ this.symm
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [commKer, xF1, xF2]
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy, inner_sub_left]; ring
  have hsw : ∫ p : Euc d × Euc d, xF1 v s a p.swap = ∫ p : Euc d × Euc d, xF1 v s a p :=
    integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
      (xF1 v s a)
  have e2 : ∫ p : Euc d × Euc d, xF2 v s a p = -∫ p : Euc d × Euc d, xF1 v s a p := by
    rw [← hsw]
    simp_rw [xF2_swap, integral_neg]
    ring
  have e3 : ∫ p : Euc d × Euc d, (xF1 v s a p - xF2 v s a p) =
      (∫ p : Euc d × Euc d, xF1 v s a p) - ∫ p : Euc d × Euc d, xF2 v s a p :=
    integral_sub hF1 hF2
  rw [e1, e3, e2]
  have e4 : ∫ p : Euc d × Euc d, xF1 v s a p = ∫ x, ∫ y, xF1 v s a (x, y) :=
    integral_prod (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d))) _ hF1
  rw [e4]
  have e5 : ∀ x : Euc d, ∫ y, xF1 v s a (x, y) =
      a x * ∑ i, v x i * ∫ y, kernGrad s (x - y) i * a y := by
    intro x
    have hint : ∀ i : Fin d, Integrable (fun y => v x i * (kernGrad s (x - y) i * a y)) :=
      fun i => (xkern_comp_int hd hs0 hsd a φ ha x i).const_mul _
    have : ∀ y, xF1 v s a (x, y) = a x * ∑ i, v x i * (kernGrad s (x - y) i * a y) := by
      intro y
      unfold xF1
      simp only [PiLp.inner_apply, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [real_inner_eq_re_inner]
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
  simp_rw [e5]
  ring

end HRS.Commutator.Whole.XNRS
