import HRS.MD.Cov211Metric

/-!
# Packet COV211, truncation of the quadratic test and sub-Gaussian second-moment tails

* `F1 x = x² χ(x)` with a fixed smooth cutoff `χ` (`= 1` on `[-1,1]`, `= 0` off `[-2,2]`), and the
  rescalings `FL L x = L² F1 (x / L)`; bounds `‖(FL L)^{(n)}‖ ≤ M L^{2-n}` (TeX `V:eq:response-cutoff-norm`).
* from the tail `P(|Z| > x) ≤ 4 e^{-x²/(2D)}` (the form of `response_subGaussian`): an exponential
  moment `E e^{Z²/(4D)} ≤ 5` (layer cake), hence `E[Z² - FL L Z] ≤ 40 D e^{-L²/(8D)}`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

/-- A smooth cutoff, `1` on `[-1,1]`, `0` outside `[-2,2]`. -/
def chi : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `F1 x = x² χ(x)`. -/
def F1 (x : ℝ) : ℝ := x ^ 2 * chi x

/-- `FL L x = L² F1 (x / L)`. -/
def FL (L : ℝ) (x : ℝ) : ℝ := L ^ 2 * F1 (x / L)

theorem F1_contDiff {n : ℕ∞} : ContDiff ℝ n F1 :=
  (contDiff_id.pow 2).mul chi.contDiff

theorem F1_nonneg (x : ℝ) : 0 ≤ F1 x := mul_nonneg (sq_nonneg x) chi.nonneg

theorem F1_le_sq (x : ℝ) : F1 x ≤ x ^ 2 :=
  mul_le_of_le_one_right (sq_nonneg x) chi.le_one

theorem F1_eq_sq {x : ℝ} (hx : |x| ≤ 1) : F1 x = x ^ 2 := by
  have : chi x = 1 := chi.one_of_mem_closedBall (by simpa [chi, Metric.mem_closedBall] using hx)
  simp [F1, this]

theorem F1_hasCompactSupport : HasCompactSupport F1 :=
  chi.hasCompactSupport.mul_left

theorem FL_contDiff {n : ℕ∞} (L : ℝ) : ContDiff ℝ n (FL L) := by
  unfold FL
  exact contDiff_const.mul (F1_contDiff.comp (contDiff_id.div_const L))

theorem FL_nonneg {L : ℝ} (x : ℝ) : 0 ≤ FL L x := mul_nonneg (sq_nonneg L) (F1_nonneg _)

theorem FL_eq_sq {L : ℝ} (hL : 0 < L) {x : ℝ} (hx : |x| ≤ L) : FL L x = x ^ 2 := by
  unfold FL
  rw [F1_eq_sq (by rw [abs_div, abs_of_pos hL]; exact (div_le_one hL).2 hx)]
  field_simp

theorem FL_le_sq {L : ℝ} (x : ℝ) (hL : 0 < L) : FL L x ≤ x ^ 2 := by
  unfold FL
  calc L ^ 2 * F1 (x / L) ≤ L ^ 2 * (x / L) ^ 2 :=
        mul_le_mul_of_nonneg_left (F1_le_sq _) (sq_nonneg L)
    _ = x ^ 2 := by field_simp

/-- Bounds for the iterated derivatives of `F1`. -/
theorem F1_iter_bound (m : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ i ≤ m, ∀ y, ‖iteratedFDeriv ℝ i F1 y‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := F1_hasCompactSupport.exists_bound_iteratedFDeriv F1_contDiff m
  exact ⟨C + 1, by linarith, fun i hi y => (hC i hi y).trans (by linarith)⟩

/-- Rescaling: `‖(FL L)^{(n)}(x)‖ ≤ L² L^{-n} M`. -/
theorem FL_iter_norm_le {L : ℝ} (hL : 0 < L) (n : ℕ) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ n F1 y‖ ≤ M) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (FL L) x‖ ≤ L ^ 2 * (L⁻¹) ^ n * M := by
  have hF : FL L = L ^ 2 • (fun z : ℝ => F1 (L⁻¹ • z)) := by
    funext x; simp [FL, div_eq_inv_mul]
  have h1 : iteratedFDeriv ℝ n (fun z : ℝ => F1 (L⁻¹ • z)) =
      fun x => (L⁻¹) ^ n • iteratedFDeriv ℝ n F1 (L⁻¹ • x) :=
    iteratedFDeriv_comp_const_smul (L⁻¹) F1_contDiff
  have hlin : ContDiff ℝ n (fun z : ℝ => L⁻¹ • z) := by fun_prop
  have hcd : ContDiff ℝ n (fun z : ℝ => F1 (L⁻¹ • z)) :=
    (F1_contDiff (n := (n : ℕ∞))).comp hlin
  rw [hF, iteratedFDeriv_const_smul_apply hcd.contDiffAt, h1]
  simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv, abs_of_pos hL]
  rw [← mul_assoc]
  gcongr
  exact hM _

/-- Uniform bound: `‖(FL L)^{(n)}‖ ≤ M L²` for `L ≥ 1`, and `‖(FL L)'‖ ≤ M L`. -/
theorem FL_bounds (m : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ L : ℝ, 1 ≤ L →
    (∀ n ≤ m, ∀ x, ‖iteratedFDeriv ℝ n (FL L) x‖ ≤ M * L ^ 2) ∧
    (∀ x, ‖iteratedFDeriv ℝ 1 (FL L) x‖ ≤ M * L) := by
  obtain ⟨M, hM0, hM⟩ := F1_iter_bound (max m 1)
  refine ⟨M, hM0, fun L hL => ⟨fun n hn x => ?_, fun x => ?_⟩⟩
  · have hL0 : 0 < L := by linarith
    refine (FL_iter_norm_le hL0 n (hM n (hn.trans (le_max_left _ _))) x).trans ?_
    have : (L⁻¹) ^ n ≤ 1 := pow_le_one₀ (inv_nonneg.2 hL0.le) (inv_le_one_of_one_le₀ hL)
    calc L ^ 2 * (L⁻¹) ^ n * M ≤ L ^ 2 * 1 * M := by gcongr
      _ = M * L ^ 2 := by ring
  · have hL0 : 0 < L := by linarith
    refine (FL_iter_norm_le hL0 1 (hM 1 (le_max_right _ _)) x).trans ?_
    calc L ^ 2 * (L⁻¹) ^ 1 * M = M * L := by field_simp
      _ ≤ _ := le_rfl

/-- `FL L` is `M L`-Lipschitz. -/
theorem FL_lipschitz {M : ℝ} {L : ℝ} (hL : 0 < L)
    (hM : ∀ x, ‖iteratedFDeriv ℝ 1 (FL L) x‖ ≤ M * L) (x y : ℝ) :
    |FL L x - FL L y| ≤ M * L * |x - y| := by
  have hd : Differentiable ℝ (FL L) := (FL_contDiff (n := 1) L).differentiable (by norm_num)
  have hb : ∀ z ∈ (univ : Set ℝ), ‖deriv (FL L) z‖ ≤ M * L := by
    intro z _
    have := hM z
    rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one] at this
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ => hd z) hb convex_univ
    (mem_univ y) (mem_univ x)
  simpa [Real.norm_eq_abs, abs_sub_comm] using this

/-- `FL L / (Cn L²)` lies in the `C_b^j` unit ball when `Cn = (j+1) M`. -/
theorem FL_mem_cbUnitBall (j : ℕ) {M : ℝ} (hM0 : 0 < M) {L : ℝ} (hL : 1 ≤ L)
    (hM : ∀ n ≤ j, ∀ x, ‖iteratedFDeriv ℝ n (FL L) x‖ ≤ M * L ^ 2) :
    (fun x => FL L x / (((j : ℝ) + 1) * M * L ^ 2)) ∈ CbUnitBall ℝ j := by
  have hL0 : 0 < L := by linarith
  set Cn : ℝ := ((j : ℝ) + 1) * M * L ^ 2 with hCn
  have hCn0 : 0 < Cn := by positivity
  have hfun : (fun x => FL L x / Cn) = Cn⁻¹ • FL L := by
    funext x; simp [div_eq_inv_mul]
  have hder : ∀ n, ∀ x, ‖iteratedFDeriv ℝ n (fun x => FL L x / Cn) x‖ =
      Cn⁻¹ * ‖iteratedFDeriv ℝ n (FL L) x‖ := by
    intro n x
    rw [hfun, iteratedFDeriv_const_smul_apply (FL_contDiff L).contDiffAt, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hCn0)]
  refine ⟨(FL_contDiff L).div_const Cn, fun n hn => ⟨Cn⁻¹ * (M * L ^ 2), ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    simp only [hder]
    exact mul_le_mul_of_nonneg_left (hM n hn x) (inv_nonneg.2 hCn0.le)
  · unfold cbNorm
    have : ∀ n ∈ Finset.range (j + 1),
        (⨆ z : ℝ, ‖iteratedFDeriv ℝ n (fun x => FL L x / Cn) z‖) ≤ Cn⁻¹ * (M * L ^ 2) := by
      intro n hn
      have hn' : n ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
      refine ciSup_le fun z => ?_
      rw [hder]
      exact mul_le_mul_of_nonneg_left (hM n hn' z) (inv_nonneg.2 hCn0.le)
    refine (Finset.sum_le_sum this).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hCn]
    push_cast
    field_simp
    exact le_rfl

/-! ### The exponential moment from the tail -/

/-- `∫_0^x (t/(2D)) e^{t²/(4D)} dt = e^{x²/(4D)} - 1`. -/
theorem integral_layer (D : ℝ) (hD : 0 < D) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, (t / (2 * D)) * Real.exp (t ^ 2 / (4 * D)) =
      Real.exp (x ^ 2 / (4 * D)) - 1 := by
  have h : ∀ t ∈ Set.uIcc 0 x, HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / (4 * D)))
      ((t / (2 * D)) * Real.exp (t ^ 2 / (4 * D))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / (4 * D)) (2 * t / (4 * D)) t := by
      simpa using ((hasDerivAt_pow 2 t).div_const (4 * D))
    have := h1.exp
    convert this using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h]
  · simp
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- `∫_0^∞ (2t/D) e^{-t²/(4D)} dt = 4`. -/
theorem integral_tail_gauss (D : ℝ) (hD : 0 < D) :
    ∫ t in Ioi (0 : ℝ), (2 * t / D) * Real.exp (-(t ^ 2 / (4 * D))) = 4 ∧
    IntegrableOn (fun t : ℝ => (2 * t / D) * Real.exp (-(t ^ 2 / (4 * D)))) (Ioi 0) := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => -4 * Real.exp (-(t ^ 2 / (4 * D))))
      ((2 * t / D) * Real.exp (-(t ^ 2 / (4 * D)))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / (4 * D))) (-(2 * t / (4 * D))) t := by
      have h0 := ((hasDerivAt_pow 2 t).div_const (4 * D)).neg
      convert h0 using 1
      simp
    have := (h1.exp).const_mul (-4 : ℝ)
    convert this using 1
    field_simp
    try ring
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ (2 * t / D) * Real.exp (-(t ^ 2 / (4 * D))) := by
    intro t ht
    have : 0 < t := ht
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg (g := fun t : ℝ => -4 * Real.exp (-(t ^ 2 / (4 * D))))
    (g' := fun t => (2 * t / D) * Real.exp (-(t ^ 2 / (4 * D))))
    (by
      refine Continuous.continuousWithinAt ?_
      fun_prop) hd hnn (l := 0) (by
      have h0 : Tendsto (fun t : ℝ => -(t ^ 2 / (4 * D))) atTop atBot := by
        apply tendsto_neg_atTop_atBot.comp
        exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by positivity)
      have := (Real.tendsto_exp_atBot.comp h0).const_mul (-4 : ℝ)
      simpa using this)
  refine ⟨?_, hint⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (by
      refine Continuous.continuousWithinAt ?_
      fun_prop) hd hint (m := 0) (by
      have h0 : Tendsto (fun t : ℝ => -(t ^ 2 / (4 * D))) atTop atBot := by
        apply tendsto_neg_atTop_atBot.comp
        exact (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).atTop_div_const (by positivity)
      have := (Real.tendsto_exp_atBot.comp h0).const_mul (-4 : ℝ)
      simpa using this)]
  simp

/-- Exponential moment from the tail bound. -/
theorem expMoment_le (P : Measure ℝ) [IsProbabilityMeasure P] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (z ^ 2 / (4 * D))) ∂P ≤ 5 := by
  have hg : ∀ t : ℝ, 0 ≤ t → 0 ≤ (t / (2 * D)) * Real.exp (t ^ 2 / (4 * D)) := fun t ht => by positivity
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul P
    (f := fun z : ℝ => |z|) (g := fun t : ℝ => (t / (2 * D)) * Real.exp (t ^ 2 / (4 * D)))
    (Filter.Eventually.of_forall fun z => abs_nonneg z) measurable_abs.aemeasurable
    (fun t _ => (Continuous.intervalIntegrable (by fun_prop) _ _))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => hg t (le_of_lt ht)))
  simp_rw [integral_layer D hD] at hlayer
  have hsq : ∀ z : ℝ, |z| ^ 2 = z ^ 2 := fun z => sq_abs z
  simp_rw [hsq] at hlayer
  obtain ⟨hI, hIint⟩ := integral_tail_gauss D hD
  have hbound : ∫⁻ t in Ioi (0 : ℝ), P {a | t < |a|} *
      ENNReal.ofReal ((t / (2 * D)) * Real.exp (t ^ 2 / (4 * D))) ≤ 4 := by
    calc ∫⁻ t in Ioi (0 : ℝ), P {a | t < |a|} *
          ENNReal.ofReal ((t / (2 * D)) * Real.exp (t ^ 2 / (4 * D)))
        ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((2 * t / D) * Real.exp (-(t ^ 2 / (4 * D)))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
          calc P {a | t < |a|} * ENNReal.ofReal ((t / (2 * D)) * Real.exp (t ^ 2 / (4 * D)))
              ≤ ENNReal.ofReal (4 * Real.exp (-t ^ 2 / (2 * D))) *
                ENNReal.ofReal ((t / (2 * D)) * Real.exp (t ^ 2 / (4 * D))) := by
                gcongr
                exact htail t ht0
            _ = ENNReal.ofReal ((2 * t / D) * Real.exp (-(t ^ 2 / (4 * D)))) := by
                rw [← ENNReal.ofReal_mul (by positivity)]
                congr 1
                have : Real.exp (-t ^ 2 / (2 * D)) * Real.exp (t ^ 2 / (4 * D)) =
                    Real.exp (-(t ^ 2 / (4 * D))) := by
                  rw [← Real.exp_add]; congr 1; field_simp; ring
                calc 4 * Real.exp (-t ^ 2 / (2 * D)) * (t / (2 * D) * Real.exp (t ^ 2 / (4 * D)))
                    = 4 * (t / (2 * D)) * (Real.exp (-t ^ 2 / (2 * D)) * Real.exp (t ^ 2 / (4 * D))) := by ring
                  _ = _ := by rw [this]; field_simp; ring
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), (2 * t / D) * Real.exp (-(t ^ 2 / (4 * D)))) := by
          rw [ofReal_integral_eq_lintegral_ofReal hIint
            ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => by
              have : 0 < t := ht
              positivity))]
      _ = 4 := by rw [hI]; norm_num
  have hP : ∫⁻ z, ENNReal.ofReal (Real.exp (z ^ 2 / (4 * D)) - 1) ∂P ≤ 4 := by
    rw [hlayer]; exact hbound
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (z ^ 2 / (4 * D))) ∂P
      ≤ ∫⁻ z, (1 + ENNReal.ofReal (Real.exp (z ^ 2 / (4 * D)) - 1)) ∂P := by
        refine lintegral_mono fun z => ?_
        have h1 := Real.add_one_le_exp (z ^ 2 / (4 * D))
        have h2 : 0 ≤ z ^ 2 / (4 * D) := by positivity
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
    _ = 1 + ∫⁻ z, ENNReal.ofReal (Real.exp (z ^ 2 / (4 * D)) - 1) ∂P := by
        rw [lintegral_add_left measurable_const]; simp
    _ ≤ 1 + 4 := by gcongr
    _ = 5 := by norm_num


theorem integrable_exp_of_tail (P : Measure ℝ) [IsProbabilityMeasure P] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) :
    Integrable (fun z : ℝ => Real.exp (z ^ 2 / (4 * D))) P := by
  refine ⟨(by fun_prop : Measurable (fun z : ℝ => Real.exp (z ^ 2 / (4 * D)))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)]
  exact lt_of_le_of_lt (expMoment_le P D hD htail) (by norm_num)

theorem integral_exp_le (P : Measure ℝ) [IsProbabilityMeasure P] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) :
    ∫ z, Real.exp (z ^ 2 / (4 * D)) ∂P ≤ 5 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
    (by fun_prop : Measurable (fun z : ℝ => Real.exp (z ^ 2 / (4 * D)))).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  have := expMoment_le P D hD htail
  rw [show (ENNReal.ofReal 5) = 5 by simp]
  exact this

theorem sq_le_exp (D : ℝ) (hD : 0 < D) (z : ℝ) : z ^ 2 ≤ 8 * D * Real.exp (z ^ 2 / (8 * D)) := by
  have h := Real.add_one_le_exp (z ^ 2 / (8 * D))
  have h2 : z ^ 2 / (8 * D) ≤ Real.exp (z ^ 2 / (8 * D)) := by linarith
  rw [div_le_iff₀ (by positivity)] at h2
  nlinarith

theorem integrable_sq_of_tail (P : Measure ℝ) [IsProbabilityMeasure P] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) :
    Integrable (fun z : ℝ => z ^ 2) P := by
  refine Integrable.mono' ((integrable_exp_of_tail P D hD htail).const_mul (8 * D))
    (by fun_prop : Measurable (fun z : ℝ => z ^ 2)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z)]
  refine (sq_le_exp D hD z).trans ?_
  gcongr
  · norm_num

theorem tail_sq_integral_le (P : Measure ℝ) [IsProbabilityMeasure P] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x →
      P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) {L : ℝ} (hL : 0 < L) :
    0 ≤ ∫ z, (z ^ 2 - FL L z) ∂P ∧
      ∫ z, (z ^ 2 - FL L z) ∂P ≤ 40 * D * Real.exp (-L ^ 2 / (8 * D)) := by
  have hIE := integrable_exp_of_tail P D hD htail
  have hIs := integrable_sq_of_tail P D hD htail
  have hFLi : Integrable (fun z => FL L z) P :=
    Integrable.mono' hIs ((FL_contDiff (n := 0) L).continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (FL_nonneg z)]; exact FL_le_sq z hL)
  refine ⟨integral_nonneg fun z => sub_nonneg.2 (FL_le_sq z hL), ?_⟩
  have hpt : ∀ z, z ^ 2 - FL L z ≤ (8 * D * Real.exp (-L ^ 2 / (8 * D))) *
      Real.exp (z ^ 2 / (4 * D)) := by
    intro z
    have hpos : 0 ≤ (8 * D * Real.exp (-L ^ 2 / (8 * D))) * Real.exp (z ^ 2 / (4 * D)) := by positivity
    by_cases hz : |z| ≤ L
    · rw [FL_eq_sq hL hz]; simpa using hpos
    · push Not at hz
      have h1 : z ^ 2 - FL L z ≤ z ^ 2 := by linarith [FL_nonneg (L := L) z]
      refine h1.trans ((sq_le_exp D hD z).trans ?_)
      have hLz : L ^ 2 ≤ z ^ 2 := by
        have := sq_lt_sq' (by linarith [abs_nonneg z]) hz
        rw [sq_abs] at this; exact this.le
      have h3 : 0 ≤ (z ^ 2 - L ^ 2) / (8 * D) := div_nonneg (by linarith) (by positivity)
      have h4 : -L ^ 2 / (8 * D) + z ^ 2 / (4 * D) - z ^ 2 / (8 * D) = (z ^ 2 - L ^ 2) / (8 * D) := by
        ring
      have hexp : Real.exp (z ^ 2 / (8 * D)) ≤
          Real.exp (-L ^ 2 / (8 * D)) * Real.exp (z ^ 2 / (4 * D)) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      calc 8 * D * Real.exp (z ^ 2 / (8 * D))
          ≤ 8 * D * (Real.exp (-L ^ 2 / (8 * D)) * Real.exp (z ^ 2 / (4 * D))) := by gcongr
        _ = _ := by ring
  calc ∫ z, (z ^ 2 - FL L z) ∂P ≤ ∫ z, (8 * D * Real.exp (-L ^ 2 / (8 * D))) *
        Real.exp (z ^ 2 / (4 * D)) ∂P :=
        integral_mono (hIs.sub hFLi) (hIE.const_mul _) hpt
    _ = (8 * D * Real.exp (-L ^ 2 / (8 * D))) * ∫ z, Real.exp (z ^ 2 / (4 * D)) ∂P :=
        integral_const_mul _ _
    _ ≤ (8 * D * Real.exp (-L ^ 2 / (8 * D))) * 5 := by
        gcongr; exact integral_exp_le P D hD htail
    _ = _ := by ring

/-- The second-moment difference is controlled by the test `FL L` up to the tail. -/
theorem abs_sq_diff_le (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (D : ℝ) (hD : 0 < D)
    (htP : ∀ x : ℝ, 0 ≤ x → P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    (htQ : ∀ x : ℝ, 0 ≤ x → Q {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))))
    {L : ℝ} (hL : 0 < L) :
    |∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| ≤
      |∫ z, FL L z ∂P - ∫ z, FL L z ∂Q| + 40 * D * Real.exp (-L ^ 2 / (8 * D)) := by
  have hFLi : ∀ (R : Measure ℝ) [IsProbabilityMeasure R],
      (∀ x : ℝ, 0 ≤ x → R {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
      Integrable (fun z => FL L z) R := by
    intro R _ htR
    exact Integrable.mono' (integrable_sq_of_tail R D hD htR)
      ((FL_contDiff (n := 0) L).continuous.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (FL_nonneg z)]; exact FL_le_sq z hL)
  have eP : ∫ z, z ^ 2 ∂P = ∫ z, FL L z ∂P + ∫ z, (z ^ 2 - FL L z) ∂P := by
    have iS : Integrable (fun z : ℝ => z ^ 2 - FL L z) P :=
      (integrable_sq_of_tail P D hD htP).sub (hFLi P htP)
    rw [← integral_add (hFLi P htP) iS]
    simp
  have eQ : ∫ z, z ^ 2 ∂Q = ∫ z, FL L z ∂Q + ∫ z, (z ^ 2 - FL L z) ∂Q := by
    have iS : Integrable (fun z : ℝ => z ^ 2 - FL L z) Q :=
      (integrable_sq_of_tail Q D hD htQ).sub (hFLi Q htQ)
    rw [← integral_add (hFLi Q htQ) iS]
    simp
  obtain ⟨a0, a1⟩ := tail_sq_integral_le P D hD htP hL
  obtain ⟨b0, b1⟩ := tail_sq_integral_le Q D hD htQ hL
  rw [eP, eQ, abs_le]
  have h1 := neg_abs_le (∫ z, FL L z ∂P - ∫ z, FL L z ∂Q)
  have h2 := le_abs_self (∫ z, FL L z ∂P - ∫ z, FL L z ∂Q)
  constructor <;> linarith

end HRS.MD.Cov211
