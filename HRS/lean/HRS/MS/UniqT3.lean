import HRS.Whole.AppendixALemmas
import HRS.Whole.AppendixAAdjoint

/-!
# T3 of `UniqPlan.md`: `forwardPairing` commutes with superposition of mollified test functions

`forwardPairing_superpose`: for `u` with uniformly bounded local `L²` mass, `ρ(t-σ)`, the drift
coordinates `C¹`, `ρ(t-σ)` and its gradient `O(⟨y⟩^{-(d+3)})`, `η ∈ C_c^∞`, `ψ'` continuous with
compact support,
`∫ ψ'(x) forwardPairing(u, η(x-·)) dx = forwardPairing(u, ∫ ψ'(x) η(x-·) dx)`.
(Evenness, nonnegativity and normalization of `η`, and `ψ' ∈ C²_c`, are not needed.)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqT3

open HRS HRS.Whole HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- The weight `(1+|y|)^{-(d+2)}`. -/
def wt (d : ℕ) (y : Euc d) : ℝ := (1 + ‖y‖) ^ (-((d : ℝ) + 2))

theorem wt_pos (y : Euc d) : 0 < wt d y := by unfold wt; positivity

theorem wt_integrable : Integrable (wt d) (volume : Measure (Euc d)) := by
  have := integrable_one_add_norm (E := Euc d) (μ := volume) (r := (d : ℝ) + 2)
    (by simp)
  exact this

theorem wt_ball_le (y c : Euc d) (h : ‖c - y‖ < 1) : (2 : ℝ) ^ (-((d : ℝ) + 2)) * wt d y ≤ wt d c := by
  unfold wt
  have h1 : 1 + ‖c‖ ≤ 2 * (1 + ‖y‖) := by
    have := norm_le_norm_add_norm_sub' c y
    have h2 : ‖c‖ ≤ ‖y‖ + ‖c - y‖ := by
      have := norm_add_le y (c - y)
      simpa using this
    linarith [norm_nonneg y]
  rw [← Real.mul_rpow (by norm_num) (by positivity)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by have : (0:ℝ) ≤ d := Nat.cast_nonneg d; linarith)

theorem enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · exact (le_self_pow₀ h two_ne_zero).trans le_add_self

theorem key_fin {u : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) (B : ℝ)
    (hB : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal B) :
    ∫⁻ y, ‖u y‖ₑ * ENNReal.ofReal (wt d y) < ⊤ := by
  set V : ℝ≥0∞ := volume (ball (0 : Euc d) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set a : ℝ := (d : ℝ) + 2 with ha
  set F : Euc d → Euc d → ℝ≥0∞ := fun y c =>
    if dist c y < 1 then ‖u y‖ₑ * ENNReal.ofReal (wt d c) else 0 with hF
  have hmeas : AEMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : AEMeasurable (fun p : Euc d × Euc d => ‖u p.1‖ₑ) (volume.prod volume) :=
      hu.enorm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    have h2 : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (wt d p.2)) := by
      unfold wt; fun_prop
    have h3 : MeasurableSet {p : Euc d × Euc d | dist p.2 p.1 < 1} :=
      measurableSet_lt (by fun_prop) measurable_const
    have := (h1.mul h2.aemeasurable).indicator h3
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [hF, Set.indicator_apply, Function.uncurry]
  have hswap := lintegral_lintegral_swap hmeas
  -- pointwise lower bound
  have h1 : ∀ y, V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y))) ≤
      ∫⁻ c, F y c := by
    intro y
    have : ∫⁻ c, F y c = ∫⁻ c in ball y 1, ‖u y‖ₑ * ENNReal.ofReal (wt d c) := by
      rw [← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun c => ?_
      by_cases h : dist c y < 1
      · rw [Set.indicator_of_mem (mem_ball.2 h)]; simp [hF, h]
      · rw [Set.indicator_of_notMem (by rw [mem_ball]; exact h)]; simp [hF, h]
    rw [this]
    calc V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y)))
        = ∫⁻ c in ball y 1, ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y)) := by
          rw [setLIntegral_const, Measure.addHaar_ball_center volume y, hV, mul_comm]
      _ ≤ _ := by
          refine setLIntegral_mono' measurableSet_ball fun c hc => ?_
          have := wt_ball_le y c (by rw [← dist_eq_norm]; exact mem_ball.1 hc)
          calc _ = ‖u y‖ₑ * ENNReal.ofReal ((2 : ℝ) ^ (-a) * wt d y) := by
                rw [ENNReal.ofReal_mul (by positivity)]; ring
            _ ≤ _ := by gcongr
  have h2 : ∀ c, ∫⁻ y, F y c ≤ ENNReal.ofReal (wt d c) * (V + ENNReal.ofReal B) := by
    intro c
    have : ∫⁻ y, F y c = ENNReal.ofReal (wt d c) * ∫⁻ y in ball c 1, ‖u y‖ₑ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_ball]
      refine lintegral_congr fun y => ?_
      by_cases h : dist c y < 1
      · rw [Set.indicator_of_mem (mem_ball.2 (by rwa [dist_comm]))]; simp [hF, h, mul_comm]
      · rw [Set.indicator_of_notMem (by rw [mem_ball, dist_comm]; exact h)]; simp [hF, h]
    rw [this]
    gcongr
    calc ∫⁻ y in ball c 1, ‖u y‖ₑ ≤ ∫⁻ y in ball c 1, (1 + ‖u y‖ₑ ^ 2) :=
          lintegral_mono fun y => enorm_le_one_add_sq _
      _ = V + ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul, hV,
            Measure.addHaar_ball_center]
      _ ≤ _ := by gcongr; exact hB c
  have h3 : V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * ∫⁻ y, ‖u y‖ₑ * ENNReal.ofReal (wt d y)) ≤
      (V + ENNReal.ofReal B) * ∫⁻ c, ENNReal.ofReal (wt d c) := by
    calc _ = ∫⁻ y, V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * (‖u y‖ₑ * ENNReal.ofReal (wt d y))) := by
          rw [lintegral_const_mul' _ _ hVt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ∫⁻ y, ∫⁻ c, F y c := lintegral_mono h1
      _ = ∫⁻ c, ∫⁻ y, F y c := hswap
      _ ≤ ∫⁻ c, ENNReal.ofReal (wt d c) * (V + ENNReal.ofReal B) := lintegral_mono h2
      _ = _ := by rw [lintegral_mul_const' _ _ (by simp [hVt]), mul_comm]
  have hwt : ∫⁻ c, ENNReal.ofReal (wt d c) < ⊤ := wt_integrable.lintegral_lt_top
  have h4 : V * (ENNReal.ofReal ((2 : ℝ) ^ (-a))) ≠ 0 := by
    refine mul_ne_zero hV0 ?_
    simpa [ENNReal.ofReal_eq_zero] using Real.rpow_pos_of_pos two_pos (-a)
  have h5 : V * (ENNReal.ofReal ((2 : ℝ) ^ (-a)) * ∫⁻ y, ‖u y‖ₑ * ENNReal.ofReal (wt d y)) < ⊤ :=
    lt_of_le_of_lt h3 (ENNReal.mul_lt_top (ENNReal.add_lt_top.2 ⟨hVt.lt_top, ENNReal.ofReal_lt_top⟩) hwt)
  rw [← mul_assoc] at h5
  by_contra hI
  rw [not_lt, top_le_iff] at hI
  rw [hI, ENNReal.mul_top h4] at h5
  exact lt_irrefl _ h5

theorem uw_int {u : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) (B : ℝ)
    (hB : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal B) :
    Integrable (fun y => ‖u y‖ * wt d y) volume := by
  refine ⟨hu.norm.mul wt_integrable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have := key_fin hu B hB
  refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) this
  rw [enorm_mul, enorm_norm, Real.enorm_of_nonneg (wt_pos y).le]

/-- Uniform local `L²` mass gives integrability against the weight `wt`. -/
theorem key_int {u h : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) (B : ℝ)
    (hB : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal B)
    (hh : AEStronglyMeasurable h volume) (C : ℝ) (hC : ∀ y, |h y| ≤ C * wt d y) :
    Integrable (fun y => u y * h y) volume := by
  refine Integrable.mono' (g := fun y => C * (‖u y‖ * wt d y)) ((uw_int hu B hB).const_mul C)
    (hu.mul hh) (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc ‖u y‖ * |h y| ≤ ‖u y‖ * (C * wt d y) := by gcongr; exact hC y
    _ = _ := by rw [Real.norm_eq_abs]; ring

/-! ### The Riesz kernel: measurability, growth, and the smoothed kernels `g * h` -/

theorem g_meas (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  split_ifs
  · exact (Real.measurable_log.comp measurable_norm).neg
  · exact (measurable_norm).pow_const _

theorem g_big {s : ℝ} (hs : 0 ≤ s) (z : Euc d) (hz : 1 ≤ ‖z‖) : |rieszKernel d s z| ≤ ‖z‖ := by
  unfold rieszKernel
  split_ifs
  · rw [abs_neg, abs_of_nonneg (Real.log_nonneg hz)]
    exact (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  · rw [abs_of_nonneg (by positivity)]
    exact (Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)).trans hz

theorem g_dom {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ G0 : Euc d → ℝ, Integrable G0 ∧ (∀ z, 0 ≤ G0 z) ∧ ∀ z, |rieszKernel d s z| ≤ G0 z + ‖z‖ := by
  set g := rieszKernel d s with hg
  have hloc : IntegrableOn (fun z => |g z|) (ball (0 : Euc d) 1) :=
    ((rieszKernel_locallyIntegrable hs0 hsd).integrableOn_isCompact (isCompact_closedBall 0 1)
      |>.mono_set ball_subset_closedBall).abs
  have hG0n : ∀ z, 0 ≤ (ball (0 : Euc d) 1).indicator (fun z => |g z|) z :=
    fun z => Set.indicator_nonneg (fun _ _ => abs_nonneg _) z
  refine ⟨_, hloc.integrable_indicator measurableSet_ball, hG0n, fun z => ?_⟩
  by_cases hz : ‖z‖ < 1
  · rw [Set.indicator_of_mem (mem_ball_zero_iff.2 hz)]; linarith [norm_nonneg z]
  · exact (g_big hs0 z (not_lt.1 hz)).trans (by linarith [hG0n z])

theorem g_int_ball {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (y : Euc d) (R : ℝ) :
    Integrable ((closedBall (0 : Euc d) R).indicator (fun t => rieszKernel d s (y - t))) := by
  obtain ⟨G0, hG0i, hG0n, hgG⟩ := g_dom (d := d) hs0 hsd
  rw [integrable_indicator_iff measurableSet_closedBall]
  have hb : IntegrableOn (fun t : Euc d => G0 (y - t) + ‖y - t‖) (closedBall (0 : Euc d) R) :=
    (hG0i.comp_sub_left y).integrableOn.add
      ((continuous_const.sub continuous_id).norm.continuousOn.integrableOn_compact (isCompact_closedBall 0 R))
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun t => ?_)
  · exact ((g_meas s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hgG _

/-- `convFun g h` grows at most linearly, for `h` continuous with compact support. -/
theorem conv_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) : ∃ C, ∀ r, |HRS.Whole.convFun (rieszKernel d s) h r| ≤ C * (1 + ‖r‖) := by
  set g := rieszKernel d s with hg
  obtain ⟨R1, hR1⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R0 : ℝ := max R1 0 with hR0def
  have hR : 0 ≤ R0 := le_max_right _ _
  have hR0 : tsupport h ⊆ closedBall (0 : Euc d) R0 :=
    hR1.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨G0, hG0i, hG0n, hgG⟩ := g_dom (d := d) hs0 hsd
  set Vcb : ℝ := (volume (closedBall (0 : Euc d) R0)).toReal with hVcb
  have hcbi : Integrable ((closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M * (∫ z, G0 z) + M * Vcb * (1 + R0), fun r => ?_⟩
  set bd : Euc d → ℝ := fun t => M * G0 (r - t) + M * (‖r‖ + R0) *
    (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) t with hbd
  have hbdi : Integrable bd := ((hG0i.comp_sub_left r).const_mul M).add (hcbi.const_mul _)
  have hle : ∀ t, ‖g (r - t) * h t‖ ≤ bd t := by
    intro t
    by_cases ht : h t = 0
    · rw [ht, mul_zero, norm_zero]
      have : 0 ≤ M * (‖r‖ + R0) * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) t := by
        exact mul_nonneg (mul_nonneg hM0 (add_nonneg (norm_nonneg _) hR))
          (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      exact add_nonneg (mul_nonneg hM0 (hG0n _)) this
    · have htc : t ∈ closedBall (0 : Euc d) R0 := hR0 (subset_tsupport h ht)
      have htn : ‖t‖ ≤ R0 := by simpa using htc
      have h1 : ‖r - t‖ ≤ ‖r‖ + R0 := (norm_sub_le _ _).trans (by linarith)
      rw [norm_mul, Real.norm_eq_abs, hbd]
      simp only [Set.indicator_of_mem htc, mul_one]
      calc |g (r - t)| * ‖h t‖ ≤ (G0 (r - t) + (‖r‖ + R0)) * M :=
            mul_le_mul ((hgG _).trans (by linarith)) (hM t) (norm_nonneg _) (by linarith [hG0n (r - t), norm_nonneg r, norm_nonneg t])
        _ = _ := by ring
  have h1 := norm_integral_le_of_norm_le hbdi (Filter.Eventually.of_forall hle)
  have h2 : ∫ t, bd t = M * (∫ z, G0 z) + M * (‖r‖ + R0) * Vcb := by
    rw [hbd, integral_add ((hG0i.comp_sub_left r).const_mul M) (hcbi.const_mul _),
      integral_const_mul, integral_const_mul, integral_sub_left_eq_self G0 volume r,
      integral_indicator measurableSet_closedBall]
    simp [hVcb, Measure.real]
  rw [Real.norm_eq_abs] at h1
  calc _ = |∫ t, g (r - t) * h t| := rfl
    _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := by
      have hI0 : 0 ≤ ∫ z, G0 z := integral_nonneg hG0n
      have hV0 : 0 ≤ Vcb := ENNReal.toReal_nonneg
      nlinarith [mul_nonneg hM0 hI0, mul_nonneg hM0 hV0, norm_nonneg r, mul_nonneg (mul_nonneg hM0 hV0) (norm_nonneg r)]

/-! ### Convolutions with `C_c^∞` functions -/

/-- The `i`-th partial derivative. -/
def D1 (i : Fin d) (h : Euc d → ℝ) : Euc d → ℝ := fun v => fderiv ℝ h v (EuclideanSpace.single i 1)

/-- `(f * h)(y) = ∫ f(x) h(y-x) dx`. -/
def cv (f h : Euc d → ℝ) (y : Euc d) : ℝ := ∫ x, f x * h (y - x)

structure Cc (h : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ h
  supp : HasCompactSupport h

theorem Cc.cont {h : Euc d → ℝ} (hh : Cc h) : Continuous h := hh.smooth.continuous

theorem Cc.D1 {h : Euc d → ℝ} (hh : Cc h) (i : Fin d) : Cc (D1 i h) :=
  ⟨(hh.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const,
    (hh.supp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (by simp)⟩

theorem cv_eq (f h : Euc d → ℝ) :
    cv f h = convolution f h (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext y; simp [cv, convolution_def]

theorem Cc.cv {f h : Euc d → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hh : Cc h) :
    Cc (cv f h) := by
  rw [cv_eq]
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable
  exact ⟨hh.supp.contDiff_convolution_right _ hfl hh.smooth,
    hfc.convolution _ hh.supp⟩

theorem cv_D1 {f h : Euc d → ℝ} (hf : Continuous f) (hh : Cc h) (i : Fin d) :
    D1 i (cv f h) = cv f (D1 i h) := by
  funext y
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable
  have hd := hh.supp.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hfl (hh.smooth.of_le (by simp)) y
  have hint := (hh.supp.fderiv (𝕜 := ℝ)).convolutionExists_right
    (ContinuousLinearMap.precompR (Euc d) (ContinuousLinearMap.mul ℝ ℝ)) hfl
    (hh.smooth.continuous_fderiv (by simp)) y
  unfold HRS.MS.UniqT3.D1
  rw [cv_eq, hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp [cv]

/-- Fubini: `g * (f ⋆ h) = f ⋆ (g * h)`. -/
theorem K_cv {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f h : Euc d → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hh : Continuous h) (hhc : HasCompactSupport h) (y : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (cv f h) y =
      cv f (HRS.Whole.convFun (rieszKernel d s) h) y := by
  set g := rieszKernel d s with hg
  obtain ⟨Rf, hRf⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Rh, hRh⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Mf, hMf⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨Mh, hMh⟩ := hh.bounded_above_of_compact_support hhc
  set F : Euc d → Euc d → ℝ := fun t x => g (y - t) * (f x * h (t - x)) with hF
  have hFm : Measurable (Function.uncurry F) := by
    have : Measurable (fun p : Euc d × Euc d => g (y - p.1)) :=
      (g_meas s).comp (measurable_const.sub measurable_fst)
    exact this.mul ((hf.measurable.comp measurable_snd).mul
      (hh.measurable.comp (measurable_fst.sub measurable_snd)))
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hA := g_int_ball hs0 hsd y (Rf + Rh)
    have hB : Integrable ((closedBall (0 : Euc d) Rf).indicator (fun _ => (1 : ℝ))) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    refine ((hA.norm.mul_prod hB).const_mul (Mf * Mh)).mono' hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨t, x⟩ := p
    simp only [Function.uncurry_apply_pair, hF]
    have hM0f : 0 ≤ Mf := (norm_nonneg _).trans (hMf 0)
    have hM0h : 0 ≤ Mh := (norm_nonneg _).trans (hMh 0)
    by_cases hz : f x * h (t - x) = 0
    · have h0 : g (y - t) * (f x * h (t - x)) = 0 := by rw [hz, mul_zero]
      rw [h0, norm_zero]
      exact mul_nonneg (mul_nonneg hM0f hM0h)
        (mul_nonneg (norm_nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _))
    · have hx : f x ≠ 0 := left_ne_zero_of_mul hz
      have hth : h (t - x) ≠ 0 := right_ne_zero_of_mul hz
      have hx' : ‖x‖ ≤ Rf := by simpa using hRf (subset_tsupport f hx)
      have ht' : ‖t - x‖ ≤ Rh := by simpa using hRh (subset_tsupport h hth)
      have htm : t ∈ closedBall (0 : Euc d) (Rf + Rh) := by
        have : ‖t‖ ≤ ‖t - x‖ + ‖x‖ := by
          simpa using norm_add_le (t - x) x
        simpa using (by linarith : ‖t‖ ≤ Rf + Rh)
      rw [Set.indicator_of_mem htm, Set.indicator_of_mem (by simpa using hx' : x ∈ closedBall (0 : Euc d) Rf),
        norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      simp only [norm_norm, mul_one, Real.norm_eq_abs]
      have := hMf x
      have := hMh (t - x)
      rw [Real.norm_eq_abs] at *
      calc _ ≤ |g (y - t)| * (Mf * Mh) := by gcongr
        _ = _ := by ring
  calc HRS.Whole.convFun g (cv f h) y = ∫ t, ∫ x, F t x := by
        unfold HRS.Whole.convFun cv
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [hF]; rw [integral_const_mul]
    _ = ∫ x, ∫ t, F t x := integral_integral_swap hint
    _ = cv f (HRS.Whole.convFun g h) y := by
        unfold cv HRS.Whole.convFun
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hF]
        have : ∀ t, g (y - t) * (f x * h (t - x)) = f x * (g (y - t) * h (t - x)) := fun t => by ring
        simp_rw [this]
        rw [integral_const_mul]
        congr 1
        rw [← integral_sub_right_eq_self (fun t' => g (y - x - t') * h t') x]
        simp only [sub_sub_sub_cancel_right]

/-! ### The outer Fubini step -/

/-- Admissible density families `R x y`: jointly continuous and dominated by `wt` uniformly for
`x ∈ tsupport ψ'`. -/
def Adm (ψ' : Euc d → ℝ) (R : Euc d → Euc d → ℝ) : Prop :=
  Continuous (Function.uncurry R) ∧ ∃ C, ∀ x ∈ tsupport ψ', ∀ y, |R x y| ≤ C * wt d y

theorem outer_fubini {u : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) (B : ℝ)
    (hB : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal B)
    {ψ' : Euc d → ℝ} (hψ : Continuous ψ') (hψc : HasCompactSupport ψ') {R : Euc d → Euc d → ℝ}
    (hR : Adm ψ' R) :
    Integrable (fun x => ψ' x * ∫ y, u y * R x y) volume ∧
      ∫ x, ψ' x * ∫ y, u y * R x y = ∫ y, u y * ∫ x, ψ' x * R x y := by
  obtain ⟨hRc, C, hC⟩ := hR
  obtain ⟨M, hM⟩ := hψ.bounded_above_of_compact_support hψc
  set F : Euc d → Euc d → ℝ := fun x y => ψ' x * (u y * R x y) with hF
  have hmeas : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : Euc d × Euc d => u p.2) (volume.prod volume) :=
      hu.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    exact (hψ.comp continuous_fst).aestronglyMeasurable.mul (h1.mul hRc.aestronglyMeasurable)
  have hint : Integrable (Function.uncurry F) (volume.prod volume) := by
    have hB' : Integrable ((tsupport ψ').indicator (fun _ => (1 : ℝ))) :=
      (integrable_indicator_iff hψc.isCompact.measurableSet).2
        (integrableOn_const hψc.isCompact.measure_lt_top.ne)
    refine (((hB'.mul_prod (uw_int hu B hB))).const_mul (M * C)).mono' hmeas
      (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p
    simp only [Function.uncurry_apply_pair, hF]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    by_cases hx : x ∈ tsupport ψ'
    · rw [Set.indicator_of_mem hx, one_mul, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have h1 := hM x
      rw [Real.norm_eq_abs] at h1
      have h2 := hC x hx y
      have hw := (wt_pos y).le
      calc |ψ' x| * (|u y| * |R x y|) ≤ M * (|u y| * (C * wt d y)) := by gcongr
        _ = _ := by ring
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, norm_zero, Set.indicator_of_notMem hx]
      simp
  refine ⟨hint.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · simp only [hF, Function.uncurry_apply_pair]; rw [integral_const_mul]
  · have := integral_integral_swap hint
    simp only [hF] at this
    calc _ = ∫ x, ∫ y, ψ' x * (u y * R x y) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp only; rw [integral_const_mul]
      _ = ∫ y, ∫ x, ψ' x * (u y * R x y) := this
      _ = _ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only
          rw [← integral_const_mul]
          congr 1; funext x; ring

theorem adm_zero (ψ' : Euc d → ℝ) : Adm ψ' (fun _ _ => 0) :=
  ⟨continuous_const, 0, fun x _ y => by simp⟩

theorem Adm.add {ψ' : Euc d → ℝ} {R R' : Euc d → Euc d → ℝ} (h : Adm ψ' R) (h' : Adm ψ' R') :
    Adm ψ' (fun x y => R x y + R' x y) := by
  obtain ⟨hc, C, hC⟩ := h
  obtain ⟨hc', C', hC'⟩ := h'
  refine ⟨hc.add hc', C + C', fun x hx y => ?_⟩
  calc _ ≤ |R x y| + |R' x y| := abs_add_le _ _
    _ ≤ C * wt d y + C' * wt d y := add_le_add (hC x hx y) (hC' x hx y)
    _ = _ := by ring

theorem Adm.sum {ι : Type*} {ψ' : Euc d → ℝ} (t : Finset ι) {R : ι → Euc d → Euc d → ℝ}
    (h : ∀ i ∈ t, Adm ψ' (R i)) : Adm ψ' (fun x y => ∑ i ∈ t, R i x y) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using adm_zero ψ'
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem adm_loc {ψ' : Euc d → ℝ} (hψc : HasCompactSupport ψ') {c h : Euc d → ℝ}
    (hc : Continuous c) (hh : Continuous h) (hhc : HasCompactSupport h) :
    Adm ψ' (fun x y => c y * h (y - x)) := by
  refine ⟨(hc.comp continuous_snd).mul (hh.comp (continuous_snd.sub continuous_fst)), ?_⟩
  obtain ⟨R1, hR1⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Rh, hRh⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Mh, hMh⟩ := hh.bounded_above_of_compact_support hhc
  set P : ℝ := max (R1 + Rh) 0 with hP
  have hP0 : 0 ≤ P := le_max_right _ _
  obtain ⟨Mc, hMc⟩ := (isCompact_closedBall (0 : Euc d) P).exists_bound_of_continuousOn hc.continuousOn
  have hMh0 : 0 ≤ Mh := (norm_nonneg _).trans (hMh 0)
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc 0 (by simpa using hP0))
  set a : ℝ := (d : ℝ) + 2 with ha
  have ha0 : 0 ≤ a := by positivity
  refine ⟨Mc * Mh * (1 + P) ^ a, fun x hx y => ?_⟩
  have hw : 0 < wt d y := wt_pos y
  by_cases hz : h (y - x) = 0
  · simp only [hz, mul_zero, abs_zero]
    positivity
  · have hx' : ‖x‖ ≤ R1 := by simpa using hR1 hx
    have hy' : ‖y - x‖ ≤ Rh := by simpa using hRh (subset_tsupport h hz)
    have hyP : ‖y‖ ≤ P := by
      have : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
      exact (by linarith : ‖y‖ ≤ R1 + Rh).trans (le_max_left _ _)
    have h1 := hMc y (by simpa using hyP)
    have h2 := hMh (y - x)
    rw [Real.norm_eq_abs] at h1 h2
    have h3 : (1 + P) ^ (-a) ≤ wt d y := by
      unfold wt
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h4 : (1 + P) ^ a * (1 + P) ^ (-a) = 1 := by
      rw [Real.rpow_neg (by positivity), mul_inv_cancel₀ (by positivity)]
    rw [abs_mul]
    calc |c y| * |h (y - x)| ≤ Mc * Mh := by gcongr
      _ = Mc * Mh * ((1 + P) ^ a * (1 + P) ^ (-a)) := by rw [h4, mul_one]
      _ ≤ Mc * Mh * (1 + P) ^ a * wt d y := by
          rw [← mul_assoc]; gcongr

theorem adm_nl {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ' : Euc d → ℝ} (hψc : HasCompactSupport ψ')
    {c h : Euc d → ℝ} (hc : Continuous c) (Cc : ℝ)
    (hcd : ∀ y, |c y| ≤ Cc * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Adm ψ' (fun x y => c y * HRS.Whole.convFun (rieszKernel d s) h (y - x)) := by
  have hcont : Continuous (HRS.Whole.convFun (rieszKernel d s) h) := by
    have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
    have := hhc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hh hl
    convert this using 1
    funext y
    simp only [HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1; funext t; ring
  refine ⟨(hc.comp continuous_snd).mul (hcont.comp (continuous_snd.sub continuous_fst)), ?_⟩
  obtain ⟨R1, hR1⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Cq, hCq⟩ := conv_bound hs0 hsd hh hhc
  have hCq0 : 0 ≤ Cq := by
    have := hCq 0
    simp only [norm_zero, add_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  have hCc0 : 0 ≤ Cc := by
    have := hcd 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨Cc * Cq * (1 + R1), fun x hx y => ?_⟩
  have hx' : ‖x‖ ≤ R1 := by simpa using hR1 hx
  have hR10 : 0 ≤ R1 := (norm_nonneg _).trans hx'
  have h1 : 1 + ‖y - x‖ ≤ (1 + R1) * (1 + ‖y‖) := by
    have : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
    nlinarith [norm_nonneg y]
  have h2 : (1 + ‖y‖) ^ (-((d : ℝ) + 3)) * (1 + ‖y‖) = wt d y := by
    unfold wt
    rw [show -((d : ℝ) + 2) = -((d : ℝ) + 3) + 1 by ring, Real.rpow_add_one (by positivity)]
  rw [abs_mul]
  calc |c y| * |HRS.Whole.convFun (rieszKernel d s) h (y - x)|
      ≤ (Cc * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (Cq * (1 + ‖y - x‖)) :=
        mul_le_mul (hcd y) (hCq _) (abs_nonneg _) (by positivity)
    _ ≤ (Cc * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) * (Cq * ((1 + R1) * (1 + ‖y‖))) := by gcongr
    _ = Cc * Cq * (1 + R1) * wt d y := by rw [← h2]; ring

/-- Linearity of the outer integral over the three groups of terms of `forwardPairing`. -/
theorem assemble {u : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) (B : ℝ)
    (hB : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal B)
    {ψ' : Euc d → ℝ} (hψ : Continuous ψ') (hψc : HasCompactSupport ψ') (ν : ℝ)
    (M : Fin d → Fin d → ℝ) {R1 R2 : Euc d → Euc d → ℝ}
    {R3 : Fin d → Fin d → Euc d → Euc d → ℝ}
    (h1 : Adm ψ' R1) (h2 : Adm ψ' R2) (h3 : ∀ i j, Adm ψ' (R3 i j)) :
    ∫ x, ψ' x * (ν * (∫ y, u y * R1 x y) - (∫ y, u y * R2 x y) -
        ∑ i, ∑ j, M j i * (∫ y, u y * R3 i j x y)) =
      ν * (∫ y, u y * ∫ x, ψ' x * R1 x y) - (∫ y, u y * ∫ x, ψ' x * R2 x y) -
        ∑ i, ∑ j, M j i * (∫ y, u y * ∫ x, ψ' x * R3 i j x y) := by
  obtain ⟨i1, e1⟩ := outer_fubini hu B hB hψ hψc h1
  obtain ⟨i2, e2⟩ := outer_fubini hu B hB hψ hψc h2
  have i3 := fun i j => (outer_fubini hu B hB hψ hψc (h3 i j)).1
  have e3 := fun i j => (outer_fubini hu B hB hψ hψc (h3 i j)).2
  have hpt : ∀ x, ψ' x * (ν * (∫ y, u y * R1 x y) - (∫ y, u y * R2 x y) -
        ∑ i, ∑ j, M j i * (∫ y, u y * R3 i j x y)) =
      ν * (ψ' x * ∫ y, u y * R1 x y) - ψ' x * (∫ y, u y * R2 x y) -
        ∑ i, ∑ j, M j i * (ψ' x * ∫ y, u y * R3 i j x y) := by
    intro x
    have : ψ' x * ∑ i, ∑ j, M j i * (∫ y, u y * R3 i j x y) =
        ∑ i, ∑ j, M j i * (ψ' x * ∫ y, u y * R3 i j x y) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [mul_sub, mul_sub, this]; ring
  simp_rw [hpt]
  have iS : Integrable (fun x => ∑ i, ∑ j, M j i * (ψ' x * ∫ y, u y * R3 i j x y)) volume :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (i3 i j).const_mul _
  have iA : Integrable (fun x => ν * (ψ' x * ∫ y, u y * R1 x y) - ψ' x * (∫ y, u y * R2 x y)) volume :=
    (i1.const_mul ν).sub i2
  rw [integral_sub iA iS, integral_sub (i1.const_mul ν) i2,
    integral_const_mul, e1, e2, integral_finset_sum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (i3 i j).const_mul _]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (i3 i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, e3]


/-! ### Jets, translation, and the final statement -/

theorem lap_eq {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (y : Euc d) :
    Laplacian.laplacian ψ y = ∑ i, D1 i (D1 i ψ) y := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold D1
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem convFun_diff {g F : Euc d → ℝ} (hg : LocallyIntegrable g volume) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) : Differentiable ℝ (HRS.Whole.convFun g F) := by
  have hconv : HRS.Whole.convFun g F = convolution F g (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext y
    simp only [HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1; funext t; ring
  rw [hconv]
  exact fun y => (hFc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hF hg y).differentiableAt

theorem convFun_D1 {g F : Euc d → ℝ} (hg : LocallyIntegrable g volume) (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) (j : Fin d) (y : Euc d) :
    D1 j (HRS.Whole.convFun g F) y = HRS.Whole.convFun g (D1 j F) y := by
  have := HRS.Whole.AppendixA.q09_conv_grad g F hg hFc hF y j
  rw [HRS.Whole.AppendixA.q09_gradient_apply] at this
  show fderiv ℝ (HRS.Whole.convFun g F) y (EuclideanSpace.single j 1) = _
  rw [this]
  unfold HRS.Whole.convFun
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [D1]; ring

theorem D1_contDiff {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (i : Fin d) : ContDiff ℝ 1 (D1 i ψ) :=
  (hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem D1_supp {ψ : Euc d → ℝ} (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (D1 i ψ) :=
  (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (by simp)

theorem fp_formula (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ) (hs0 : 0 ≤ D.s)
    (hsd : D.s < d) (u : Euc d → ℝ) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ)
    (hb : ∀ i, ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ (t - σ)) y i))
    (hρ : ContDiff ℝ 1 (ρ (t - σ))) :
    forwardPairing D ρ t σ u ψ =
      D.invβ * (∫ y, u y * ∑ i, D1 i (D1 i ψ) y) -
      (∫ y, u y * ∑ i, (D1 i (fun y => meanFieldDriftW D (ρ (t - σ)) y i) y * ψ y +
          meanFieldDriftW D (ρ (t - σ)) y i * D1 i ψ y)) -
      ∑ i, ∑ j, D.M j i * (∫ y, u y * (D1 j (ρ (t - σ)) y *
          HRS.Whole.convFun (rieszKernel d D.s) (D1 i ψ) y +
          ρ (t - σ) y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y)) := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have h1 : (∫ x, u x * Laplacian.laplacian ψ x) = ∫ y, u y * ∑ i, D1 i (D1 i ψ) y := by
    congr 1; funext x; rw [lap_eq hψ]
  have h2 : (∫ x, u x * ∑ i : Fin d, fderiv ℝ (fun y => meanFieldDriftW D (ρ (t - σ)) y i * ψ y) x
      (EuclideanSpace.single i (1 : ℝ))) = ∫ y, u y * ∑ i, (D1 i (fun y => meanFieldDriftW D (ρ (t - σ)) y i) y * ψ y +
          meanFieldDriftW D (ρ (t - σ)) y i * D1 i ψ y) := by
    congr 1; funext y; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_fun_mul ((hb i).differentiable (by norm_num) y) (hψd y)]
    simp only [D1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have h3 : ∀ i j, (∫ x, u x * fderiv ℝ (fun y => ρ (t - σ) y * kernelConvDeriv d D.s i ψ y) x
        (EuclideanSpace.single j (1 : ℝ))) = ∫ y, u y * (D1 j (ρ (t - σ)) y *
          HRS.Whole.convFun (rieszKernel d D.s) (D1 i ψ) y +
          ρ (t - σ) y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i ψ)) y) := by
    intro i j
    congr 1; funext y; congr 1
    have hK : kernelConvDeriv d D.s i ψ = HRS.Whole.convFun (rieszKernel d D.s) (D1 i ψ) := rfl
    rw [hK, fderiv_fun_mul (hρ.differentiable (by norm_num) y)
      (convFun_diff hl (D1_contDiff hψ i) (D1_supp hψc i) y)]
    have := convFun_D1 hl (D1_contDiff hψ i) (D1_supp hψc i) j y
    simp only [D1, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at this ⊢
    rw [this]; ring
  unfold forwardPairing
  rw [h1, h2]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h3]


theorem D1_shift (i : Fin d) (h : Euc d → ℝ) (x : Euc d) :
    D1 i (fun y => h (y - x)) = fun y => D1 i h (y - x) := by
  funext y; simp only [D1]; rw [fderiv_comp_sub]

theorem conv_shift (g F : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.convFun g (fun y => F (y - x)) = fun y => HRS.Whole.convFun g F (y - x) := by
  funext y
  unfold HRS.Whole.convFun
  rw [← integral_sub_right_eq_self (fun t' => g (y - x - t') * F t') x]
  simp only [sub_sub_sub_cancel_right]

theorem K_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {h : Euc d → ℝ} (hh : Continuous h)
    (hhc : HasCompactSupport h) : Continuous (HRS.Whole.convFun (rieszKernel d s) h) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have := hhc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hh hl
  convert this using 1
  funext y
  simp only [HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
  congr 1; funext t; ring

theorem cv_integrable {ψ' h : Euc d → ℝ} (hψ : Continuous ψ') (hψc : HasCompactSupport ψ')
    (hh : Continuous h) (y : Euc d) : Integrable (fun x => ψ' x * h (y - x)) volume :=
  (hψ.mul (hh.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
    (hψc.mul_right)

theorem cv_lin {ψ' : Euc d → ℝ} (hψ : Continuous ψ') (hψc : HasCompactSupport ψ') (a b : ℝ)
    {h1 h2 : Euc d → ℝ} (c1 : Continuous h1) (c2 : Continuous h2) (y : Euc d) :
    cv ψ' (fun v => a * h1 v + b * h2 v) y = a * cv ψ' h1 y + b * cv ψ' h2 y := by
  unfold cv
  have i1 := (cv_integrable hψ hψc c1 y).const_mul a
  have i2 := (cv_integrable hψ hψc c2 y).const_mul b
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]
  congr 1; funext x; ring

theorem cv_sum {ι : Type*} {ψ' : Euc d → ℝ} (hψ : Continuous ψ') (hψc : HasCompactSupport ψ')
    (t : Finset ι) (h : ι → Euc d → ℝ) (hc : ∀ i, Continuous (h i)) (y : Euc d) :
    ∫ x, ψ' x * ∑ i ∈ t, h i (y - x) = ∑ i ∈ t, cv ψ' (h i) y := by
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ fun i _ => cv_integrable hψ hψc (hc i) y]
  rfl


theorem Adm.congr {ψ' : Euc d → ℝ} {R R' : Euc d → Euc d → ℝ} (h : Adm ψ' R)
    (e : ∀ x y, R x y = R' x y) : Adm ψ' R' := by
  have : R = R' := funext fun x => funext fun y => e x y
  rwa [← this]

/-- Density of the Laplacian term for the profile `θ(· - x)`. -/
def R1 (θ : Euc d → ℝ) (x y : Euc d) : ℝ := ∑ i, D1 i (D1 i θ) (y - x)

/-- Density of the transport term. -/
def R2 (b : Fin d → Euc d → ℝ) (θ : Euc d → ℝ) (x y : Euc d) : ℝ :=
  ∑ i, (D1 i (b i) y * θ (y - x) + b i y * D1 i θ (y - x))

/-- Density of the nonlocal term. -/
def R3 (s : ℝ) (ρt θ : Euc d → ℝ) (i j : Fin d) (x y : Euc d) : ℝ :=
  D1 j ρt y * HRS.Whole.convFun (rieszKernel d s) (D1 i θ) (y - x) +
    ρt y * HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i θ)) (y - x)

theorem forwardPairing_superpose (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ) (t σ : ℝ)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hb : ∀ i, ContDiff ℝ 1 (fun y => meanFieldDriftW D (ρ (t - σ)) y i))
    (hρ : ContDiff ℝ 1 (ρ (t - σ))) (Cρ : ℝ)
    (hρ0 : ∀ y, |ρ (t - σ) y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (hρ1 : ∀ y, ‖fderiv ℝ (ρ (t - σ)) y‖ ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))
    (u : Euc d → ℝ) (hu : AEStronglyMeasurable u volume) (B : ℝ)
    (hB : ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal B)
    (η : Euc d → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (ψ' : Euc d → ℝ) (hψ : Continuous ψ') (hψc : HasCompactSupport ψ') :
    ∫ x, ψ' x * forwardPairing D ρ t σ u (fun y => η (x - y)) =
      forwardPairing D ρ t σ u (fun y => ∫ x, ψ' x * η (x - y)) := by
  set ρt : Euc d → ℝ := ρ (t - σ) with hρt
  set b : Fin d → Euc d → ℝ := fun i y => meanFieldDriftW D ρt y i with hbdef
  set θ : Euc d → ℝ := fun v => η (-v) with hθdef
  have hθ : Cc θ := ⟨hη.comp contDiff_neg, hηc.comp_homeomorph (Homeomorph.neg (Euc d))⟩
  have hfam : ∀ x, (fun y => η (x - y)) = fun y => θ (y - x) := by
    intro x; funext y; simp [hθdef, neg_sub]
  have hΦ : (fun y => ∫ x, ψ' x * η (x - y)) = cv ψ' θ := by
    funext y; simp [cv, hθdef, neg_sub]
  have hΦcc : Cc (cv ψ' θ) := hθ.cv hψ hψc
  have hsm : ∀ x, ContDiff ℝ 2 (fun y => θ (y - x)) := fun x =>
    (hθ.smooth.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
  have hsp : ∀ x, HasCompactSupport (fun y => θ (y - x)) := fun x =>
    hθ.supp.comp_homeomorph (Homeomorph.subRight x)
  have hLHS : ∀ x, forwardPairing D ρ t σ u (fun y => η (x - y)) =
      D.invβ * (∫ y, u y * R1 θ x y) - (∫ y, u y * R2 b θ x y) -
        ∑ i, ∑ j, D.M j i * (∫ y, u y * R3 D.s ρt θ i j x y) := by
    intro x
    rw [hfam x, fp_formula D ρ t σ hs0 hsd u (hsm x) (hsp x) hb hρ]
    simp only [D1_shift, conv_shift, R1, R2, R3]
    rfl
  -- admissibility
  have hbc : ∀ i, Continuous (b i) := fun i => (hb i).continuous
  have hDb : ∀ i, Continuous (D1 i (b i)) := fun i =>
    ((hb i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDρ : ∀ j, Continuous (D1 j ρt) := fun j =>
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hA1 : Adm ψ' (R1 θ) := by
    refine (Adm.sum (Finset.univ : Finset (Fin d))
      (R := fun i x y => (fun _ => (1 : ℝ)) y * D1 i (D1 i θ) (y - x)) fun i _ =>
        adm_loc hψc continuous_const (hθ.D1 i |>.D1 i).cont (hθ.D1 i |>.D1 i).supp).congr ?_
    intro x y; simp [R1]
  have hA2 : Adm ψ' (R2 b θ) := by
    refine (Adm.sum (Finset.univ : Finset (Fin d))
      (R := fun i x y => D1 i (b i) y * θ (y - x) + b i y * D1 i θ (y - x)) fun i _ =>
        (adm_loc hψc (hDb i) hθ.cont hθ.supp).add (adm_loc hψc (hbc i) (hθ.D1 i).cont (hθ.D1 i).supp)).congr ?_
    intro x y; simp [R2]
  have hnorm : ∀ j y, |D1 j ρt y| ≤ Cρ * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := fun j y => by
    refine le_trans ?_ (hρ1 y)
    unfold D1
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    simp
  have hA3 : ∀ i j, Adm ψ' (R3 D.s ρt θ i j) := fun i j =>
    ((adm_nl hs0 hsd hψc (hDρ j) Cρ (hnorm j) (hθ.D1 i).cont (hθ.D1 i).supp).add
      (adm_nl hs0 hsd hψc hρ.continuous Cρ hρ0 ((hθ.D1 i).D1 j).cont ((hθ.D1 i).D1 j).supp)).congr
      (fun x y => rfl)
  simp_rw [hLHS]
  rw [assemble hu B hB hψ hψc D.invβ D.M hA1 hA2 hA3, hΦ,
    fp_formula D ρ t σ hs0 hsd u (hΦcc.smooth.of_le (by simp)) hΦcc.supp hb hρ]
  have c0 := hθ.cont
  have P1 : ∀ y, ∫ x, ψ' x * R1 θ x y = ∑ i, D1 i (D1 i (cv ψ' θ)) y := by
    intro y
    have c1 : ∀ i, Continuous (fun v => D1 i (D1 i θ) v) := fun i => (hθ.D1 i |>.D1 i).cont
    show ∫ x, ψ' x * ∑ i, D1 i (D1 i θ) (y - x) = _
    rw [cv_sum hψ hψc Finset.univ (fun i => D1 i (D1 i θ)) c1 y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cv_D1 hψ hθ i, cv_D1 hψ (hθ.D1 i) i]
  have P2 : ∀ y, ∫ x, ψ' x * R2 b θ x y =
      ∑ i, (D1 i (b i) y * cv ψ' θ y + b i y * D1 i (cv ψ' θ) y) := by
    intro y
    show ∫ x, ψ' x * ∑ i, (D1 i (b i) y * θ (y - x) + b i y * D1 i θ (y - x)) = _
    have c2 : ∀ i, Continuous (fun v => D1 i (b i) y * θ v + b i y * D1 i θ v) := fun i => by
      have := (hθ.D1 i).cont
      fun_prop
    rw [cv_sum hψ hψc Finset.univ (fun i v => D1 i (b i) y * θ v + b i y * D1 i θ v) c2 y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cv_lin hψ hψc _ _ hθ.cont (hθ.D1 i).cont y, cv_D1 hψ hθ i]
  have P3 : ∀ i j y, ∫ x, ψ' x * R3 D.s ρt θ i j x y =
      D1 j ρt y * HRS.Whole.convFun (rieszKernel d D.s) (D1 i (cv ψ' θ)) y +
        ρt y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i (cv ψ' θ))) y := by
    intro i j y
    show cv ψ' (fun v => D1 j ρt y * HRS.Whole.convFun (rieszKernel d D.s) (D1 i θ) v +
      ρt y * HRS.Whole.convFun (rieszKernel d D.s) (D1 j (D1 i θ)) v) y = _
    rw [cv_lin hψ hψc _ _ (K_cont hs0 hsd (hθ.D1 i).cont (hθ.D1 i).supp)
      (K_cont hs0 hsd ((hθ.D1 i).D1 j).cont ((hθ.D1 i).D1 j).supp) y,
      cv_D1 hψ hθ i, cv_D1 hψ (hθ.D1 i) j,
      K_cv hs0 hsd hψ hψc (hθ.D1 i).cont (hθ.D1 i).supp y,
      K_cv hs0 hsd hψ hψc ((hθ.D1 i).D1 j).cont ((hθ.D1 i).D1 j).supp y]
  simp only [P1, P2, P3]
  rfl


end HRS.MS.UniqT3
