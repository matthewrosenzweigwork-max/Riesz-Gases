import HRS.MS.WrDiagAux1

/-!
# WR-10 (part 1): the Hilbert feature measure and feature map of `kTau`

Packet WR-10 of `docs/WR_B_PLAN.md` (T2), namespace `HRS.MS.Wr`, helper prefix `wr10_`.

For `0 < s`, `0 < τ` let `A = ((volume|_{(τ,∞)}).withDensity (psd3_F d s · 0))` (a finite measure on `ℝ`
of mass `kTau d s τ 0`) and `featMeasure d s τ = A ⊗ stdGaussian (Euc d)` on `ℝ × Euc d`.
The feature map is
`featMap d s τ x = [(t, ξ) ↦ (cos (√(1/(2t)) ⟪ξ,x⟫), sin (√(1/(2t)) ⟪ξ,x⟫))] ∈ L²(featMeasure; ℝ²)`.

Main results in this file (`hs : 0 < s`, `hτ : 0 < τ`):

* `featMeasure_univ`: the mass of `featMeasure d s τ` is `ofReal (kTau d s τ 0)` (so it is finite);
* `featMap_inner`: `⟪featMap d s τ x, featMap d s τ y⟫ = kTau d s τ (x - y)`
  (Fubini, `Q34.gauss_kernel_eq`, `psd3_F_eq_gauss`);
* `wr10_continuous_of_inner`: a map into a real inner product space whose Gram matrix is a
  continuous difference kernel is continuous; used for `Continuous (featMap d s τ)`.

`featMap` is defined with a dependent `if` on `0 < s ∧ 0 < τ` (the function is only an `L²` element when
the measure is finite; in the other case the value is `0`, never used).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.Wr

open HRS.Whole HRS.MS.Psd HRS.Whole.Q34

variable {d : ℕ}

/-! ### The feature measure -/

/-- The time marginal `((volume|_{(τ,∞)}).withDensity (psd3_F d s · 0))`. -/
def featTimeMeasure (d : ℕ) (s τ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi τ)).withDensity (fun t => ENNReal.ofReal (psd3_F d s t 0))

/-- The feature measure on `ℝ × Euc d`: heat-time density times the standard Gaussian. -/
def featMeasure (d : ℕ) (s τ : ℝ) : Measure (ℝ × Euc d) :=
  (featTimeMeasure d s τ).prod (stdGaussian (Euc d))

theorem wr10_psd3_F_zero_meas (s : ℝ) : Measurable (fun t : ℝ => psd3_F d s t (0 : Euc d)) :=
  psd3_F_meas_t (d := d) s 0

theorem featTimeMeasure_univ {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    featTimeMeasure d s τ univ = ENNReal.ofReal (kTau d s τ 0) := by
  unfold featTimeMeasure kTau
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [ofReal_integral_eq_lintegral_ofReal (psd3_F_zero_integrableOn (d := d) hs hτ)]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact psd3_F_nonneg hs (lt_trans hτ ht).le 0

theorem isFiniteMeasure_featTimeMeasure {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    IsFiniteMeasure (featTimeMeasure d s τ) :=
  ⟨by rw [featTimeMeasure_univ hs hτ]; exact ENNReal.ofReal_lt_top⟩

theorem isFiniteMeasure_featMeasure {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    IsFiniteMeasure (featMeasure d s τ) := by
  have := isFiniteMeasure_featTimeMeasure (d := d) hs hτ
  unfold featMeasure
  infer_instance

/-- The mass of the feature measure is `kTau d s τ 0`. -/
theorem featMeasure_univ {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    featMeasure d s τ univ = ENNReal.ofReal (kTau d s τ 0) := by
  unfold featMeasure
  rw [← Set.univ_prod_univ, Measure.prod_prod, featTimeMeasure_univ hs hτ, measure_univ, mul_one]

theorem featMeasure_real_univ {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    (featMeasure d s τ).real univ = kTau d s τ 0 := by
  rw [measureReal_def, featMeasure_univ hs hτ, ENNReal.toReal_ofReal (kTau_nonneg hs hτ 0)]

/-! ### The feature function -/

/-- The phase `√(1/(2t)) ⟪ξ,x⟫` at the point `(t,ξ)`. -/
def featAng (x : Euc d) (p : ℝ × Euc d) : ℝ := Real.sqrt (1 / (2 * p.1)) * inner ℝ p.2 x

/-- The pointwise feature `(cos, sin)(√(1/(2t)) ⟪ξ,x⟫) ∈ ℝ²`. -/
def featFun (x : Euc d) (p : ℝ × Euc d) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (featAng x p), Real.sin (featAng x p)]

theorem featAng_meas (x : Euc d) : Measurable (featAng x) := by
  unfold featAng
  have h1 : Measurable (fun p : ℝ × Euc d => p.1) := measurable_fst
  have h2 : Measurable (fun p : ℝ × Euc d => (inner ℝ p.2 x : ℝ)) :=
    (continuous_snd.inner continuous_const).measurable
  exact (Real.continuous_sqrt.measurable.comp (measurable_const.div (measurable_const.mul h1))).mul h2

theorem featFun_meas (x : Euc d) : Measurable (featFun x) := by
  unfold featFun
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp ?_
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · exact Real.measurable_cos.comp (featAng_meas x)
  · exact Real.measurable_sin.comp (featAng_meas x)

theorem featFun_norm (x : Euc d) (p : ℝ × Euc d) : ‖featFun x p‖ = 1 := by
  unfold featFun
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_two]

theorem featFun_inner (x y : Euc d) (p : ℝ × Euc d) :
    inner ℝ (featFun x p) (featFun y p) = Real.cos (featAng x p - featAng y p) := by
  unfold featFun
  simp [PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

theorem featMem {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    MemLp (featFun x) 2 (featMeasure d s τ) := by
  have := isFiniteMeasure_featMeasure (d := d) hs hτ
  refine MemLp.of_bound (featFun_meas x).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p => ?_)
  rw [featFun_norm]

/-- The Hilbert feature map `Euc d → L²(featMeasure; ℝ²)`. -/
def featMap (d : ℕ) (s τ : ℝ) (x : Euc d) : Lp (EuclideanSpace ℝ (Fin 2)) 2 (featMeasure d s τ) :=
  if h : 0 < s ∧ 0 < τ then (featMem h.1 h.2 x).toLp (featFun x) else 0

theorem featMap_coeFn {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x : Euc d) :
    (featMap d s τ x : ℝ × Euc d → EuclideanSpace ℝ (Fin 2)) =ᵐ[featMeasure d s τ] featFun x := by
  unfold featMap
  split_ifs with h
  · exact MemLp.coeFn_toLp _
  · exact absurd ⟨hs, hτ⟩ h

/-! ### Gram matrix: `⟪Ψ x, Ψ y⟫ = kTau (x - y)` -/

theorem wr10_gauss_inner {t : ℝ} (ht : 0 < t) (x y : Euc d) :
    ∫ ξ : Euc d, Real.cos (featAng x (t, ξ) - featAng y (t, ξ)) ∂(stdGaussian (Euc d)) =
      Real.exp (-(1 / (4 * t)) * ‖x - y‖ ^ 2) := by
  have hτ : 0 < 1 / (4 * t) := by positivity
  rw [gauss_kernel_eq hτ x y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [featAng]
  have : Real.sqrt (2 * (1 / (4 * t))) = Real.sqrt (1 / (2 * t)) := by
    congr 1; field_simp; ring
  rw [this, ← mul_sub]

theorem featMap_inner_integral {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x y : Euc d) :
    ∫ p, inner ℝ (featFun x p) (featFun y p) ∂(featMeasure d s τ) = kTau d s τ (x - y) := by
  have := isFiniteMeasure_featTimeMeasure (d := d) hs hτ
  simp only [featFun_inner]
  have hmeas : Measurable (fun p : ℝ × Euc d => Real.cos (featAng x p - featAng y p)) :=
    Real.measurable_cos.comp ((featAng_meas x).sub (featAng_meas y))
  have hint : Integrable (fun p : ℝ × Euc d => Real.cos (featAng x p - featAng y p))
      (featMeasure d s τ) := by
    have := isFiniteMeasure_featMeasure (d := d) hs hτ
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  unfold featMeasure
  rw [integral_prod _ (by simpa [featMeasure] using hint)]
  have h1 : ∀ᵐ t ∂(featTimeMeasure d s τ),
      ∫ ξ : Euc d, Real.cos (featAng x (t, ξ) - featAng y (t, ξ)) ∂(stdGaussian (Euc d)) =
        Real.exp (-(1 / (4 * t)) * ‖x - y‖ ^ 2) := by
    have : ∀ᵐ t ∂(featTimeMeasure d s τ), 0 < t := by
      unfold featTimeMeasure
      refine ae_withDensity_iff (ENNReal.measurable_ofReal.comp
        (wr10_psd3_F_zero_meas (d := d) s)) |>.2 ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht _ using lt_trans hτ ht
    filter_upwards [this] with t ht using wr10_gauss_inner ht x y
  rw [integral_congr_ae h1]
  unfold featTimeMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun t => ENNReal.ofReal (psd3_F d s t (0 : Euc d)))
    (ENNReal.measurable_ofReal.comp (wr10_psd3_F_zero_meas (d := d) s))
    (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  unfold kTau
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans hτ ht
  rw [ENNReal.toReal_ofReal (psd3_F_nonneg hs ht0.le 0), smul_eq_mul, psd3_F_eq_gauss ht0 (x - y)]

/-- **Gram identity** `⟪Ψ x, Ψ y⟫ = kTau (x - y)` for the feature map. -/
theorem featMap_inner {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) (x y : Euc d) :
    inner ℝ (featMap d s τ x) (featMap d s τ y) = kTau d s τ (x - y) := by
  rw [MeasureTheory.L2.inner_def]
  rw [← featMap_inner_integral hs hτ x y]
  refine integral_congr_ae ?_
  filter_upwards [featMap_coeFn hs hτ x, featMap_coeFn hs hτ y] with p h1 h2
  rw [h1, h2]

/-! ### Continuity from the Gram identity -/

/-- A map into a real inner product space whose Gram matrix is a continuous difference kernel
`k (x - y)` is continuous: `‖Ψ x - Ψ y‖² = 2 k 0 - 2 k (x - y)`. -/
theorem wr10_continuous_of_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Ψ : Euc d → H} {k : Euc d → ℝ} (hk : Continuous k)
    (hΨ : ∀ x y : Euc d, inner ℝ (Ψ x) (Ψ y) = k (x - y)) : Continuous Ψ := by
  rw [continuous_iff_continuousAt]
  intro x0
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hsq : ∀ x : Euc d, dist (Ψ x) (Ψ x0) ^ 2 = 2 * k 0 - 2 * k (x - x0) := by
    intro x
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_sub_right, hΨ x x, hΨ x x0, hΨ x0 x, hΨ x0 x0]
    have : k (x0 - x) = k (x - x0) := by
      have h1 := hΨ x0 x
      rw [real_inner_comm] at h1
      rw [← h1, hΨ x x0]
    simp only [sub_self, this]
    ring
  have hlim : Tendsto (fun x : Euc d => 2 * k 0 - 2 * k (x - x0)) (𝓝 x0) (𝓝 0) := by
    have h1 : Continuous (fun x : Euc d => 2 * k 0 - 2 * k (x - x0)) := by fun_prop
    have h2 := h1.tendsto x0
    simpa using h2
  have h3 : Tendsto (fun x : Euc d => Real.sqrt (2 * k 0 - 2 * k (x - x0))) (𝓝 x0) (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hlim
  refine h3.congr fun x => ?_
  rw [← hsq x, Real.sqrt_sq dist_nonneg]

end HRS.MS.Wr
