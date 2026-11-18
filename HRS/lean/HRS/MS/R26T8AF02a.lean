import HRS.MS.R26T8AF00
import HRS.MS.UniqN0b
import HRS.MS.SuppU2Aux2
import HRS.MS.SuppU2Aux3
import HRS.MS.AdjConvAux1
import HRS.MS.UlTail
import HRS.MH.ScreenedS3
import HRS.MS.MovOscAux2
import HRS.MS.S82RA2

/-!
# S8.2 observed-time layer, packet T8A.F02a: Fourier representation of the actual odd convolution

`forceConv i h = (∇g * h)_i` (cancellation convention, `s = d/2`) equals `g * ∂_i h` (Riesz potential of the derivative),
hence has the Fourier symbol `c 2π ξ_i |ξ|^{-s}` (merged `kg_fourier_h_proof`).  The identification is by regularising
`g_ε = (|z|² + ε²)^{-s/2}`: integration by parts against the smooth `g_ε` and dominated convergence (the oddness of
`∂_i g_ε` removes the subtraction `h(x)` on the unit-scale ball exactly).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- regularised kernel -/
def r26t8a_f02a_g (s ε : ℝ) (z : Euc d) : ℝ := (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2)

/-- its `i`-th partial derivative -/
def r26t8a_f02a_k (s ε : ℝ) (i : Fin d) (z : Euc d) : ℝ := -(s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1)) * z i

theorem r26t8a_f02a_hasFDerivAt (s : ℝ) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    HasFDerivAt (r26t8a_f02a_g s ε)
      ((-(s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1))) • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y‖ ^ 2 + ε ^ 2) ((2 : ℝ) • innerSL ℝ z) z :=
    (u2_hasFDerivAt_normSq z).add_const _
  have hpos : (‖z‖ ^ 2 + ε ^ 2) ≠ 0 := by positivity
  have h2 := h1.rpow_const (p := -s / 2) (Or.inl hpos)
  refine h2.congr_fderiv ?_
  ext v
  simp
  ring

theorem r26t8a_f02a_g_cont (s : ℝ) {ε : ℝ} (hε : 0 < ε) : Continuous (r26t8a_f02a_g (d := d) s ε) := by
  unfold r26t8a_f02a_g
  exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by positivity)

theorem r26t8a_f02a_k_cont (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) :
    Continuous (r26t8a_f02a_k (d := d) s ε i) := by
  unfold r26t8a_f02a_k
  refine Continuous.mul (Continuous.neg (Continuous.mul continuous_const ?_)) (by fun_prop)
  exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by positivity)

theorem r26t8a_f02a_g_le (s : ℝ) (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (z : Euc d) :
    |r26t8a_f02a_g s ε z| ≤ (ε ^ 2) ^ (-s / 2) := by
  unfold r26t8a_f02a_g
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖]) (by linarith)

theorem r26t8a_f02a_k_le (s : ℝ) (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (i : Fin d) (z : Euc d) :
    |r26t8a_f02a_k s ε i z| ≤ s * (ε ^ 2) ^ (-(s + 1) / 2) := by
  unfold r26t8a_f02a_k
  set t : ℝ := ‖z‖ ^ 2 + ε ^ 2 with ht
  have htp : 0 < t := by positivity
  have h1 : |z i| ≤ t ^ ((1 : ℝ) / 2) := by
    have : |z i| ≤ ‖z‖ := by
      have := HRS.MS.UniqN0.n0_coord_le z i
      exact this
    refine this.trans ?_
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hs, abs_of_nonneg (Real.rpow_nonneg htp.le _)]
  have h2 : t ^ (-s / 2 - 1) * |z i| ≤ t ^ (-(s + 1) / 2) := by
    calc t ^ (-s / 2 - 1) * |z i| ≤ t ^ (-s / 2 - 1) * t ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg htp.le _)
      _ = t ^ (-(s + 1) / 2) := by rw [← Real.rpow_add htp]; congr 1; ring
  have h3 : t ^ (-(s + 1) / 2) ≤ (ε ^ 2) ^ (-(s + 1) / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ‖z‖]) (by linarith)
  calc s * t ^ (-s / 2 - 1) * |z i| = s * (t ^ (-s / 2 - 1) * |z i|) := by ring
    _ ≤ s * (ε ^ 2) ^ (-(s + 1) / 2) := mul_le_mul_of_nonneg_left (h2.trans h3) hs

/-- integration by parts against the regularised kernel -/
theorem r26t8a_f02a_ibp (s : ℝ) (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (i : Fin d)
    (h : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    ∫ y, r26t8a_f02a_g s ε (x - y) * fderiv ℝ h y (EuclideanSpace.single i 1) =
      ∫ y, r26t8a_f02a_k s ε i (x - y) * h y := by
  set f : Euc d → ℝ := fun y => r26t8a_f02a_g s ε (x - y) with hf
  have hfd : ∀ y, HasFDerivAt f ((-(-(s * (‖x - y‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1))) • innerSL ℝ (x - y))) y := by
    intro y
    have h1 := r26t8a_f02a_hasFDerivAt s hε (x - y)
    have h2 : HasFDerivAt (fun y : Euc d => x - y) (-(ContinuousLinearMap.id ℝ (Euc d))) y :=
      (hasFDerivAt_const x y).sub (hasFDerivAt_id y) |>.congr_fderiv (by ext; simp)
    have := h1.comp y h2
    refine this.congr_fderiv ?_
    ext v
    simp
  have hfv : ∀ y, fderiv ℝ f y (EuclideanSpace.single i 1) = -r26t8a_f02a_k s ε i (x - y) := by
    intro y
    rw [(hfd y).fderiv]
    simp [r26t8a_f02a_k, EuclideanSpace.inner_single_right]
  have hfdiff : ∀ y, DifferentiableAt ℝ f y := fun y => (hfd y).differentiableAt
  have hint : ∀ (c : ℝ) (φ : Euc d → ℝ), Continuous φ → (∀ y, |φ y| ≤ c) → ∀ (ψ : Euc d → ℝ),
      Integrable ψ volume → Integrable (fun y => φ y * ψ y) volume := by
    intro c φ hφ hb ψ hψ
    exact hψ.bdd_mul hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y)
  have hkc : Continuous (fun y => r26t8a_f02a_k s ε i (x - y)) :=
    (r26t8a_f02a_k_cont s hε i).comp (continuous_const.sub continuous_id)
  have hgc : Continuous (fun y => r26t8a_f02a_g s ε (x - y)) :=
    (r26t8a_f02a_g_cont s hε).comp (continuous_const.sub continuous_id)
  have i1 : Integrable (fun y => fderiv ℝ f y (EuclideanSpace.single i 1) * h y) volume := by
    simp_rw [hfv, neg_mul]
    exact (hint _ _ hkc (fun y => r26t8a_f02a_k_le s hs hε i (x - y)) _ h.integrable).neg
  have hDh : Integrable (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) volume := by
    exact (HRS.MS.MovOsc.mova1_D i h).integrable
  have i2 : Integrable (fun y => f y * fderiv ℝ h y (EuclideanSpace.single i 1)) volume :=
    hint _ _ hgc (fun y => r26t8a_f02a_g_le s hs hε (x - y)) _ hDh
  have i3 : Integrable (fun y => f y * h y) volume :=
    hint _ _ hgc (fun y => r26t8a_f02a_g_le s hs hε (x - y)) _ h.integrable
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := f) (g := ⇑h)
    (v := EuclideanSpace.single i 1) i1 i2 i3 (fun y _ => hfdiff y) (fun y _ => h.differentiableAt)
  simp_rw [hfv] at key
  rw [show (∫ y, f y * fderiv ℝ (⇑h) y (EuclideanSpace.single i 1)) =
      ∫ y, r26t8a_f02a_g s ε (x - y) * fderiv ℝ h y (EuclideanSpace.single i 1) from rfl] at key
  rw [key]
  simp only [neg_mul, integral_neg, neg_neg]

/-- the subtracted version of the datum on the unit-scale ball around `x` -/
def r26t8a_f02a_ht (h : Euc d → ℝ) (x y : Euc d) : ℝ := if ‖x - y‖ ≤ 1 / 4 then h y - h x else h y

theorem r26t8a_f02a_odd (s : ℝ) (ε : ℝ) (i : Fin d) (z : Euc d) :
    r26t8a_f02a_k s ε i (-z) = -r26t8a_f02a_k s ε i z := by
  unfold r26t8a_f02a_k
  simp [norm_neg]

/-- cancellation on the ball: the oddness of the regularised kernel -/
theorem r26t8a_f02a_ball (s : ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin d) (x : Euc d) :
    ∫ y, (if ‖x - y‖ ≤ 1 / 4 then r26t8a_f02a_k s ε i (x - y) else 0) = 0 := by
  set F : Euc d → ℝ := fun z => if ‖z‖ ≤ 1 / 4 then r26t8a_f02a_k s ε i z else 0 with hF
  have hodd : ∀ z, F (-z) = -F z := by
    intro z
    simp only [hF, norm_neg]
    split_ifs
    · exact r26t8a_f02a_odd s ε i z
    · simp
  have e1 : ∫ y, (if ‖x - y‖ ≤ 1 / 4 then r26t8a_f02a_k s ε i (x - y) else 0) = ∫ z, F z :=
    integral_sub_left_eq_self F volume x
  rw [e1]
  have e2 : ∫ z, F (-z) = ∫ z, F z := integral_neg_eq_self F volume
  simp_rw [hodd, integral_neg] at e2
  linarith

theorem r26t8a_f02a_sub (s : ℝ) (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (i : Fin d)
    (h : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    ∫ y, r26t8a_f02a_k s ε i (x - y) * r26t8a_f02a_ht h x y =
      ∫ y, r26t8a_f02a_k s ε i (x - y) * h y := by
  have hkc : Continuous (fun y => r26t8a_f02a_k s ε i (x - y)) :=
    (r26t8a_f02a_k_cont s hε i).comp (continuous_const.sub continuous_id)
  have i1 : Integrable (fun y => r26t8a_f02a_k s ε i (x - y) * h y) volume :=
    h.integrable.bdd_mul hkc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact r26t8a_f02a_k_le s hs hε i (x - y))
  set F : Euc d → ℝ := fun z => if ‖z‖ ≤ 1 / 4 then r26t8a_f02a_k s ε i z else 0 with hF
  have hFi : Integrable F volume := by
    classical
    have h0 : IntegrableOn (r26t8a_f02a_k s ε i) (Metric.closedBall (0 : Euc d) (1 / 4)) volume :=
      (r26t8a_f02a_k_cont s hε i).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    have := h0.integrable_indicator Metric.isClosed_closedBall.measurableSet
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    rw [Set.indicator_apply]
    simp only [mem_closedBall_zero_iff, hF]
  have i2 : Integrable (fun y => F (x - y)) volume := hFi.comp_sub_left x
  have e : (fun y => r26t8a_f02a_k s ε i (x - y) * r26t8a_f02a_ht h x y) =
      fun y => r26t8a_f02a_k s ε i (x - y) * h y - h x * F (x - y) := by
    funext y
    unfold r26t8a_f02a_ht
    simp only [hF]
    split_ifs <;> ring
  rw [e, integral_sub i1 (i2.const_mul (h x)), integral_const_mul]
  have := r26t8a_f02a_ball s hε i x
  have e2 : ∫ y, F (x - y) = 0 := by simpa [hF] using this
  rw [e2]; ring

/-- `‖x - y‖^{-s}` times a bounded integrable function is integrable (`0 < s < d`) -/
theorem r26t8a_f02a_int_pow (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (x : Euc d)
    (ψ : Euc d → ℝ) (hψ : Integrable ψ volume) (B : ℝ) (hb : ∀ y, |ψ y| ≤ B) :
    Integrable (fun y => ‖x - y‖ ^ (-s) * ψ y) volume := by
  classical
  set near : Euc d → ℝ := fun w => if ‖w‖ < 1 then ‖w‖ ^ (-s) else 0 with hnear
  set far : Euc d → ℝ := fun w => if ‖w‖ < 1 then 0 else ‖w‖ ^ (-s) with hfar
  have hni : Integrable near volume := by
    have h0 := HRS.Whole.u2_integrableOn_ball_rpow (d := d) hd hs0 hsd
    have := h0.integrable_indicator Metric.isOpen_ball.measurableSet
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    rw [Set.indicator_apply]
    simp only [hnear, mem_ball_zero_iff]
  have hnm : Measurable near := by
    refine Measurable.ite (measurableSet_lt measurable_norm measurable_const) ?_ measurable_const
    exact measurable_norm.pow_const _
  have hfm : Measurable far := by
    refine Measurable.ite (measurableSet_lt measurable_norm measurable_const) measurable_const ?_
    exact measurable_norm.pow_const _
  have hfb : ∀ w, ‖far w‖ ≤ 1 := by
    intro w
    simp only [hfar]
    split_ifs with h
    · simp
    · push_neg at h
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)
  have h1 : Integrable (fun y => near (x - y) * ψ y) volume :=
    (hni.comp_sub_left x).mul_bdd hψ.aestronglyMeasurable (c := B) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb y) |>.congr (Filter.Eventually.of_forall fun y => by simp [mul_comm])
  have h2 : Integrable (fun y => far (x - y) * ψ y) volume :=
    hψ.bdd_mul (hfm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => hfb (x - y))
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun y => ?_)
  by_cases hlt : ‖x - y‖ < 1 <;> simp [hnear, hfar, hlt]

theorem r26t8a_f02a_sq_rpow {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ 2) ^ p = a ^ (2 * p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num

/-- pointwise limits of the regularisation -/
theorem r26t8a_f02a_g_lim (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => r26t8a_f02a_g s (1 / ((n : ℝ) + 1)) z) atTop (𝓝 (‖z‖ ^ (-s))) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc : Continuous (fun e : ℝ => (‖z‖ ^ 2 + e ^ 2) ^ (-s / 2)) :=
    Continuous.rpow_const (by fun_prop) fun e => Or.inl (by positivity)
  have := hc.tendsto 0
  have h2 := this.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have e : (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-s / 2) = ‖z‖ ^ (-s) := by
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, r26t8a_f02a_sq_rpow hp.le]
    congr 1; ring
  rw [e] at h2
  exact h2

theorem r26t8a_f02a_k_lim (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => r26t8a_f02a_k s (1 / ((n : ℝ) + 1)) i z) atTop
      (𝓝 (-(s * (‖z‖ ^ 2) ^ (-s / 2 - 1)) * z i)) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc : Continuous (fun e : ℝ => (‖z‖ ^ 2 + e ^ 2) ^ (-s / 2 - 1)) :=
    Continuous.rpow_const (by fun_prop) fun e => Or.inl (by positivity)
  have h2 := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero] at h2
  unfold r26t8a_f02a_k
  exact ((h2.const_mul s).neg).mul_const (z i)

theorem r26t8a_f02a_g_dom (s : ℝ) (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : z ≠ 0) :
    |r26t8a_f02a_g s ε z| ≤ ‖z‖ ^ (-s) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold r26t8a_f02a_g
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ‖z‖ ^ 2) (by nlinarith [sq_nonneg ε] : ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 + ε ^ 2)
    (by linarith : -s / 2 ≤ 0)
  rw [r26t8a_f02a_sq_rpow hp.le] at this
  convert this using 2; ring

theorem r26t8a_f02a_k_dom (s : ℝ) (hs : 0 ≤ s) {ε : ℝ} (hε : 0 < ε) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    |r26t8a_f02a_k s ε i z| ≤ s * ‖z‖ ^ (-s - 1) := by
  have hp : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold r26t8a_f02a_k
  rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg hs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have h1 : (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) ≤ (‖z‖ ^ 2) ^ (-s / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)
  rw [r26t8a_f02a_sq_rpow hp.le] at h1
  have h2 : |z i| ≤ ‖z‖ := HRS.MS.UniqN0.n0_coord_le z i
  have h3 : ‖z‖ ^ (2 * (-s / 2 - 1)) * ‖z‖ = ‖z‖ ^ (-s - 1) := by
    rw [← Real.rpow_add_one hp.ne']; congr 1; ring
  calc s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1) * |z i|
      ≤ s * ‖z‖ ^ (2 * (-s / 2 - 1)) * ‖z‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 hs) h2 (abs_nonneg _) (by positivity)
    _ = s * ‖z‖ ^ (-s - 1) := by rw [mul_assoc, h3]

/-- bounds for a Schwartz function and its derivative -/
theorem r26t8a_f02a_schwartz_bds (h : SchwartzMap (Euc d) ℝ) (i : Fin d) :
    (∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Euc d, |h y - h x| ≤ L * ‖y - x‖) ∧
    (∃ B : ℝ, ∀ y, |fderiv ℝ h y (EuclideanSpace.single i 1)| ≤ B) := by
  obtain ⟨C, hC0, hC⟩ := h.decay 0 1
  have hfd : ∀ x, ‖fderiv ℝ h x‖ ≤ C := fun x => by
    have := hC x
    simpa [norm_iteratedFDeriv_one] using this
  refine ⟨⟨C, hC0.le, fun x y => ?_⟩, ⟨C, fun y => ?_⟩⟩
  · have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := ⇑h) (fun z _ => h.differentiableAt) (fun z _ => hfd z) (Set.mem_univ x) (Set.mem_univ y)
    simpa [Real.norm_eq_abs] using this
  · have := (fderiv ℝ h y).le_opNorm (EuclideanSpace.single i 1)
    have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    rw [h1, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (hfd y)

theorem r26t8a_f02a_ae_ne (hd : 1 ≤ d) (x : Euc d) : ∀ᵐ y : Euc d ∂volume, x - y ≠ 0 := by
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using (by omega : 0 < d)
  filter_upwards [(Set.countable_singleton x).ae_notMem (volume : Measure (Euc d))] with y hy
  intro h0
  exact hy (by rw [Set.mem_singleton_iff]; exact (sub_eq_zero.1 h0).symm)

theorem r26t8a_f02a_limA (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (i : Fin d)
    (h : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    Tendsto (fun n : ℕ => ∫ y, r26t8a_f02a_g s (1 / ((n : ℝ) + 1)) (x - y) *
        fderiv ℝ h y (EuclideanSpace.single i 1)) atTop
      (𝓝 (∫ y, ‖x - y‖ ^ (-s) * fderiv ℝ h y (EuclideanSpace.single i 1))) := by
  obtain ⟨-, B, hB⟩ := r26t8a_f02a_schwartz_bds h i
  have hDh : Integrable (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) volume :=
    (HRS.MS.MovOsc.mova1_D i h).integrable
  have hbound : Integrable (fun y => ‖x - y‖ ^ (-s) * |fderiv ℝ h y (EuclideanSpace.single i 1)|) volume :=
    r26t8a_f02a_int_pow hd hs0 hsd x _ hDh.abs |B| (fun y => by
      rw [abs_abs]; exact (hB y).trans (le_abs_self B))
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hbound (fun n => ?_) ?_
  · have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact ((r26t8a_f02a_g_cont s hεn).comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hDh.aestronglyMeasurable
  · filter_upwards [r26t8a_f02a_ae_ne hd x] with y hy
    have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (r26t8a_f02a_g_dom s hs0.le hεn hy) (abs_nonneg _)
  · filter_upwards [r26t8a_f02a_ae_ne hd x] with y hy
    exact (r26t8a_f02a_g_lim s hy).mul_const _

theorem r26t8a_f02a_limB (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (i : Fin d)
    (h : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    Tendsto (fun n : ℕ => ∫ y, r26t8a_f02a_k s (1 / ((n : ℝ) + 1)) i (x - y) * r26t8a_f02a_ht h x y)
      atTop
      (𝓝 (∫ y, (-(s * (‖x - y‖ ^ 2) ^ (-s / 2 - 1)) * (x - y) i) * r26t8a_f02a_ht h x y)) := by
  classical
  obtain ⟨⟨L, hL0, hL⟩, -⟩ := r26t8a_f02a_schwartz_bds h i
  set ψ0 : Euc d → ℝ := fun y => if ‖x - y‖ ≤ 1 / 4 then 1 else 0 with hψ0
  have hψi : Integrable ψ0 volume := by
    have h0 : IntegrableOn (fun _ : Euc d => (1 : ℝ)) (Metric.closedBall (0 : Euc d) (1 / 4)) volume :=
      integrableOn_const (measure_closedBall_lt_top.ne)
    have := (h0.integrable_indicator Metric.isClosed_closedBall.measurableSet).comp_sub_left x
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.comp, Set.indicator_apply, mem_closedBall_zero_iff, hψ0]
  have hbi : Integrable (fun y => ‖x - y‖ ^ (-s) * ψ0 y) volume :=
    r26t8a_f02a_int_pow hd hs0 hsd x ψ0 hψi 1 (fun y => by simp only [hψ0]; split_ifs <;> simp)
  set bnd : Euc d → ℝ := fun y => s * L * (‖x - y‖ ^ (-s) * ψ0 y) + s * 4 ^ (s + 1) * |h y| with hbnd
  have hbndi : Integrable bnd volume :=
    (hbi.const_mul (s * L)).add (h.integrable.abs.const_mul (s * 4 ^ (s + 1)))
  have hhtm : Measurable (r26t8a_f02a_ht h x) := by
    unfold r26t8a_f02a_ht
    exact Measurable.ite (measurableSet_le (measurable_const.sub measurable_id).norm measurable_const)
      (h.continuous.measurable.sub measurable_const) h.continuous.measurable
  refine tendsto_integral_of_dominated_convergence bnd (fun n => ?_) hbndi (fun n => ?_) ?_
  · have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact (((r26t8a_f02a_k_cont s hεn i).comp (continuous_const.sub continuous_id)).measurable.mul
      hhtm).aestronglyMeasurable
  · filter_upwards [r26t8a_f02a_ae_ne hd x] with y hy
    have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 hy
    have hk := r26t8a_f02a_k_dom s hs0.le hεn i hy
    rw [Real.norm_eq_abs, abs_mul]
    have hs4 : 0 ≤ s * 4 ^ (s + 1) * |h y| := by positivity
    by_cases hn : ‖x - y‖ ≤ 1 / 4
    · have hht : |r26t8a_f02a_ht h x y| ≤ L * ‖x - y‖ := by
        unfold r26t8a_f02a_ht; rw [if_pos hn]
        have := hL x y
        rwa [norm_sub_rev] at this
      have e1 : s * ‖x - y‖ ^ (-s - 1) * (L * ‖x - y‖) = s * L * ‖x - y‖ ^ (-s) := by
        have : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
          rw [← Real.rpow_add_one hpos.ne']; congr 1; ring
        calc s * ‖x - y‖ ^ (-s - 1) * (L * ‖x - y‖) = s * L * (‖x - y‖ ^ (-s - 1) * ‖x - y‖) := by ring
          _ = _ := by rw [this]
      have : |r26t8a_f02a_k s (1 / ((n : ℝ) + 1)) i (x - y)| * |r26t8a_f02a_ht h x y| ≤
          s * L * ‖x - y‖ ^ (-s) :=
        (mul_le_mul hk hht (abs_nonneg _) (by positivity)).trans (le_of_eq e1)
      simp only [hbnd, hψ0, if_pos hn, mul_one]
      linarith
    · push_neg at hn
      have hht : |r26t8a_f02a_ht h x y| = |h y| := by unfold r26t8a_f02a_ht; rw [if_neg (not_le.2 hn)]
      have h4 : ‖x - y‖ ^ (-s - 1) ≤ 4 ^ (s + 1) := by
        have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 4) hn.le (by linarith : -s - 1 ≤ 0)
        calc ‖x - y‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) := this
          _ = 4 ^ (s + 1) := by
            rw [one_div, Real.inv_rpow (by norm_num), show -s - 1 = -(s + 1) by ring,
              Real.rpow_neg (by norm_num), inv_inv]
      have : |r26t8a_f02a_k s (1 / ((n : ℝ) + 1)) i (x - y)| * |r26t8a_f02a_ht h x y| ≤
          s * 4 ^ (s + 1) * |h y| := by
        rw [hht]
        calc _ ≤ (s * ‖x - y‖ ^ (-s - 1)) * |h y| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
          _ ≤ (s * 4 ^ (s + 1)) * |h y| := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hs0.le) (abs_nonneg _)
      have hb0 : 0 ≤ s * L * (‖x - y‖ ^ (-s) * ψ0 y) := by
        have : 0 ≤ ψ0 y := by simp only [hψ0]; split_ifs <;> norm_num
        positivity
      simp only [hbnd]
      linarith
  · filter_upwards [r26t8a_f02a_ae_ne hd x] with y hy
    exact (r26t8a_f02a_k_lim s i hy).mul_const _

/-- the cancellation convolution equals the Riesz potential of the derivative -/
theorem r26t8a_f02a_ident (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (i : Fin d)
    (h : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    (convGradConvW (rieszKernelGrad d s) ⇑h x) i =
      HRS.Whole.convFun (rieszKernel d s) (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) x := by
  have hd1 : 1 ≤ d := by omega
  have hint := (HRS.MS.Ul.tail_conv hd hs0.le hsd h).1 x
  have hcomp : (convGradConvW (rieszKernelGrad d s) ⇑h x) i =
      ∫ y, (HRS.MS.Ul.ultInt s (⇑h) x y) i := by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) hint
    simpa [HRS.MS.Ul.ult_conv_unfold] using this.symm
  rw [hcomp]
  have hA := r26t8a_f02a_limA hd1 hs0 hsd i h x
  have hB := r26t8a_f02a_limB hd1 hs0 hsd i h x
  have hseq : ∀ n : ℕ, ∫ y, r26t8a_f02a_k s (1 / ((n : ℝ) + 1)) i (x - y) * r26t8a_f02a_ht h x y =
      ∫ y, r26t8a_f02a_g s (1 / ((n : ℝ) + 1)) (x - y) * fderiv ℝ h y (EuclideanSpace.single i 1) := by
    intro n
    have hεn : 0 < 1 / ((n : ℝ) + 1) := by positivity
    rw [r26t8a_f02a_sub s hs0.le hεn i h x, r26t8a_f02a_ibp s hs0.le hεn i h x]
  simp_rw [hseq] at hB
  have hu := tendsto_nhds_unique hB hA
  have hconv : HRS.Whole.convFun (rieszKernel d s) (fun y => fderiv ℝ h y (EuclideanSpace.single i 1)) x =
      ∫ y, ‖x - y‖ ^ (-s) * fderiv ℝ h y (EuclideanSpace.single i 1) := by
    unfold HRS.Whole.convFun rieszKernel
    simp [hs0.ne']
  rw [hconv, ← hu]
  refine integral_congr_ae ?_
  filter_upwards [r26t8a_f02a_ae_ne hd1 x] with y hy
  unfold HRS.MS.Ul.ultInt r26t8a_f02a_ht
  have hk : rieszKernelGrad d s (x - y) i = -(s * (‖x - y‖ ^ 2) ^ (-s / 2 - 1)) * (x - y) i := by
    have := u2_kap_eq (d := d) s i hy
    unfold u2_kap at this
    rw [this, show u2_sigma s = s by simp [u2_sigma, hs0.ne']]
  by_cases hn : ‖x - y‖ ≤ 1 / 4
  · simp only [if_pos hn, PiLp.smul_apply, smul_eq_mul, hk]; ring
  · simp only [if_neg hn, PiLp.smul_apply, smul_eq_mul, hk]; ring

/-- Fourier representation of the actual odd convolution at the critical exponent, with integrability of the symbol side -/
theorem r26t8a_forceConv_fourier_int (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (h : SchwartzMap (Euc d) ℝ),
      Integrable (fun xi : Euc d => ((c * (2 * Real.pi * xi i) * ‖xi‖ ^ (-criticalS d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) xi) ∧
      ∀ x : Euc d,
      ((r26t8a_forceConv i h x : ℝ) : ℂ) =
        ∫ xi : Euc d, ((c * (2 * Real.pi * xi i) * ‖xi‖ ^ (-criticalS d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) xi *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x xi : ℝ)) := by
  have hd1 : 1 ≤ d := by omega
  have hs0' : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd' : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  obtain ⟨c, hc, H⟩ := HRS.MH.Screened.kg_fourier_h_proof hd1 hs0'.le hsd'
  have hexp : criticalS d - d = -criticalS d := by unfold criticalS; ring
  refine ⟨c, hc, fun i h => ⟨?_, fun x => ?_⟩⟩
  · have := (H i h 0).1
    rwa [hexp] at this
  · obtain ⟨-, hrep⟩ := H i h x
    rw [hexp] at hrep
    rw [← hrep, r26t8a_forceConv, r26t8a_f02a_ident hd hs0' hsd' i h x]

/-- Fourier representation of the actual odd convolution at the critical exponent -/
theorem r26t8a_forceConv_fourier (d : ℕ) (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (h : SchwartzMap (Euc d) ℝ) (x : Euc d),
      ((r26t8a_forceConv i h x : ℝ) : ℂ) =
        ∫ xi : Euc d, ((c * (2 * Real.pi * xi i) * ‖xi‖ ^ (-criticalS d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) xi *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x xi : ℝ)) := by
  obtain ⟨c, hc, H⟩ := r26t8a_forceConv_fourier_int d hd
  exact ⟨c, hc, fun i h x => (H i h).2 x⟩

end HRS.MS.R26T8A

end
