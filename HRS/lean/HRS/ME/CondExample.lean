import HRS.Equilibrium.StaticLimits
import HRS.Main.Equilibrium29Spec
import HRS.MD.EQLawFlow
import HRS.Prob.CLT

/-!
# HRS.ME.CondExample: the conditioned limit of Example 5.11 (Packet B)

Assuming the centering clause `HRS.Main.centering_transition` (as hypothesis `hCT`, `type_of%`), and
`v = C_β(ψ,ψ) > 0`, for smooth `ψ` with `s < 2d/3`:

* (B1) `P_{N,β}(Z_N > 0) → 1/2`,
* (B2) `∫ f(Z_N) dP_{N,β}(· | Z_N > 0) → ∫ f · halfNormalDensity v` for bounded continuous `f`.

Route.  The laws `ν_N = law(P_{N,β}) Z_N` converge weakly to `γ = gaussianReal 0 v.toNNReal`.  For a
bounded continuous `f`, `∫ 1_{(0,∞)} f dν_N → ∫ 1_{(0,∞)} f dγ` (`tendsto_indicator_integral`): the
indicator is squeezed between continuous functions `f · clamp(z/ε)` and the tent `max(0, 1-|z|/ε)`
(which carries no Gaussian mass in the limit).  The conditioned integral is
`(P(A_N))⁻¹ · ∫ 1_{(0,∞)} f dν_N` (`cond_integral_eq`), and `P(A_N) → 1/2` by (B1).
The Gibbs measures are probability measures for `N ≥ 1` (`HRS.MD.EQLawFlow.eqlaw_gibbs_prob`); the
sequences are shifted by one to keep all indices in range.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

noncomputable section

namespace HRS.ME.CondExample

/-! ### Continuous test functions and the squeeze -/

/-- `clamp(z/ε) = max(0, min(1, z/ε))`: continuous, `0` for `z ≤ 0`, `1` for `z ≥ ε`. -/
def clampPos (ε z : ℝ) : ℝ := max 0 (min 1 (z / ε))

/-- `max(0, 1 - |z|/ε)`: continuous, `0 ≤ · ≤ 1`, supported in `[-ε, ε]`. -/
def tentFn (ε z : ℝ) : ℝ := max 0 (1 - |z| / ε)

theorem continuous_clampPos (ε : ℝ) : Continuous (clampPos ε) :=
  continuous_const.max (continuous_const.min (continuous_id.div_const ε))

theorem continuous_tentFn (ε : ℝ) : Continuous (tentFn ε) :=
  continuous_const.max (continuous_const.sub (continuous_abs.div_const ε))

theorem clampPos_nonneg (ε z : ℝ) : 0 ≤ clampPos ε z := le_max_left _ _

theorem clampPos_le_one (ε z : ℝ) : clampPos ε z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem tentFn_nonneg (ε z : ℝ) : 0 ≤ tentFn ε z := le_max_left _ _

theorem tentFn_le_one {ε : ℝ} (hε : 0 < ε) (z : ℝ) : tentFn ε z ≤ 1 := by
  have : 0 ≤ |z| / ε := div_nonneg (abs_nonneg z) hε.le
  exact max_le zero_le_one (by linarith)

theorem clampPos_eq_zero {ε z : ℝ} (hε : 0 < ε) (hz : z ≤ 0) : clampPos ε z = 0 := by
  unfold clampPos
  have h1 : z / ε ≤ 0 := (div_le_iff₀ hε).2 (by linarith)
  have h2 : min 1 (z / ε) ≤ 0 := le_trans (min_le_right _ _) h1
  exact max_eq_left h2

theorem clampPos_eq_one {ε z : ℝ} (hε : 0 < ε) (hz : ε < z) : clampPos ε z = 1 := by
  unfold clampPos
  have h1 : 1 ≤ z / ε := (one_le_div hε).2 hz.le
  rw [min_eq_left h1]
  exact max_eq_right zero_le_one

/-- Pointwise squeeze: `|1_{(0,∞)} f - f·clamp(·/ε)| ≤ M · tent`. -/
theorem key_bound {f : ℝ → ℝ} {M0 : ℝ} (hM0 : ∀ z, |f z| ≤ M0) {ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    |indicator (Ioi 0) f z - f z * clampPos ε z| ≤ M0 * tentFn ε z := by
  have hM : 0 ≤ M0 := (abs_nonneg _).trans (hM0 0)
  rcases lt_or_ge 0 z with hz | hz
  · rw [indicator_of_mem (show z ∈ Ioi 0 from hz)]
    have hc0 := clampPos_nonneg ε z
    have hc1 := clampPos_le_one ε z
    have ht : 1 - clampPos ε z ≤ tentFn ε z := by
      unfold clampPos tentFn
      rw [abs_of_pos hz]
      rcases le_total 1 (z / ε) with h | h
      · rw [min_eq_left h, max_eq_right zero_le_one]
        linarith [le_max_left (0 : ℝ) (1 - z / ε)]
      · rw [min_eq_right h, max_eq_right (div_nonneg hz.le hε.le)]
        exact le_max_right _ _
    have e : f z - f z * clampPos ε z = f z * (1 - clampPos ε z) := by ring
    rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - clampPos ε z)]
    calc |f z| * (1 - clampPos ε z) ≤ M0 * (1 - clampPos ε z) :=
          mul_le_mul_of_nonneg_right (hM0 z) (by linarith)
      _ ≤ M0 * tentFn ε z := mul_le_mul_of_nonneg_left ht hM
  · rw [indicator_of_notMem (show z ∉ Ioi 0 from not_lt.2 hz), clampPos_eq_zero hε hz]
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hM (tentFn_nonneg ε z)

theorem integrable_of_bdd {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ} (hg : Measurable g)
    (M : ℝ) (hM : ∀ z, |g z| ≤ M) : Integrable g μ :=
  MemLp.integrable (q := 1) le_rfl
    (MemLp.of_bound hg.aestronglyMeasurable M
      (ae_of_all _ (fun z => by simpa [Real.norm_eq_abs] using hM z)))

/-- Weak convergence tested on a bounded continuous function `g`. -/
theorem conv_bc {ν : ℕ → Measure ℝ} {γ : Measure ℝ}
    (hconv : ∀ F : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, F x ∂(ν N)) atTop (𝓝 (∫ x, F x ∂γ)))
    (g : ℝ → ℝ) (hg : Continuous g) (M : ℝ) (hM : ∀ z, |g z| ≤ M) :
    Tendsto (fun N => ∫ z, g z ∂(ν N)) atTop (𝓝 (∫ z, g z ∂γ)) :=
  hconv (BoundedContinuousFunction.ofNormedAddCommGroup g hg M
    (fun z => by simpa [Real.norm_eq_abs] using hM z))

/-- `ε ↓ 0`: `∫ f·clamp(·/ε) dγ → ∫ 1_{(0,∞)} f dγ` (dominated convergence, pointwise everywhere). -/
theorem tendsto_clamp_integral {γ : Measure ℝ} [IsFiniteMeasure γ] {f : ℝ → ℝ} (hf : Continuous f)
    {M0 : ℝ} (hM0 : ∀ z, |f z| ≤ M0) :
    Tendsto (fun ε => ∫ z, f z * clampPos ε z ∂γ) (𝓝[>] 0)
      (𝓝 (∫ z, indicator (Ioi 0) f z ∂γ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M0) ?_ ?_ (integrable_const M0) ?_
  · exact Filter.Eventually.of_forall fun ε => (hf.mul (continuous_clampPos ε)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ε => ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (clampPos_nonneg ε z)]
    nlinarith [hM0 z, clampPos_le_one ε z, clampPos_nonneg ε z, abs_nonneg (f z)]
  · refine ae_of_all _ fun z => ?_
    by_cases hz : 0 < z
    · have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f z * clampPos ε z = f z := by
        filter_upwards [Ioo_mem_nhdsGT hz] with ε hε
        rw [clampPos_eq_one hε.1 hε.2, mul_one]
      rw [indicator_of_mem (show z ∈ Ioi 0 from hz)]
      exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)
    · have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f z * clampPos ε z = 0 := by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        rw [clampPos_eq_zero hε (not_lt.1 hz), mul_zero]
      rw [indicator_of_notMem (show z ∉ Ioi 0 from hz)]
      exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)

/-- `ε ↓ 0`: `∫ tent_ε dγ → 0` when `γ` has no atom at `0`. -/
theorem tendsto_tent_integral {γ : Measure ℝ} [IsFiniteMeasure γ] (h0 : ∀ᵐ z ∂γ, z ≠ 0) :
    Tendsto (fun ε => ∫ z, tentFn ε z ∂γ) (𝓝[>] 0) (𝓝 0) := by
  have key := tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε z => tentFn ε z) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const (1 : ℝ)) ?_
  · simpa using key
  · exact Filter.Eventually.of_forall fun ε => (continuous_tentFn ε).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine ae_of_all _ fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (tentFn_nonneg _ _)]
    exact tentFn_le_one hε z
  · filter_upwards [h0] with z hz
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), tentFn ε z = 0 := by
      filter_upwards [Ioo_mem_nhdsGT (abs_pos.2 hz)] with ε hε
      have h1 : 1 ≤ |z| / ε := (one_le_div hε.1).2 hε.2.le
      unfold tentFn
      rw [max_eq_left (by linarith)]
    exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)


/-- Two-sided bounds for the indicator integral against a finite measure. -/
theorem bounds_N {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ} (hf : Continuous f) {M0 : ℝ}
    (hM0 : ∀ z, |f z| ≤ M0) {ε : ℝ} (hε : 0 < ε) :
    (∫ z, f z * clampPos ε z ∂μ) - M0 * (∫ z, tentFn ε z ∂μ) ≤ ∫ z, indicator (Ioi 0) f z ∂μ ∧
    ∫ z, indicator (Ioi 0) f z ∂μ ≤ (∫ z, f z * clampPos ε z ∂μ) + M0 * (∫ z, tentFn ε z ∂μ) := by
  have hM : 0 ≤ M0 := (abs_nonneg _).trans (hM0 0)
  have hF : Integrable (fun z => f z * clampPos ε z) μ :=
    integrable_of_bdd (hf.mul (continuous_clampPos ε)).measurable M0 (fun z => by
      show |f z * clampPos ε z| ≤ M0
      rw [abs_mul, abs_of_nonneg (clampPos_nonneg ε z)]
      nlinarith [hM0 z, clampPos_le_one ε z, clampPos_nonneg ε z, abs_nonneg (f z)])
  have hT : Integrable (tentFn ε) μ :=
    integrable_of_bdd (continuous_tentFn ε).measurable 1 (fun z => by
      rw [abs_of_nonneg (tentFn_nonneg ε z)]
      exact tentFn_le_one hε z)
  have hI : Integrable (indicator (Ioi 0) f) μ :=
    integrable_of_bdd (hf.measurable.indicator measurableSet_Ioi) M0 (fun z => by
      by_cases hz : 0 < z
      · rw [indicator_of_mem (show z ∈ Ioi 0 from hz)]
        exact hM0 z
      · rw [indicator_of_notMem (show z ∉ Ioi 0 from hz)]
        simpa using hM)
  have e1 : (∫ z, f z * clampPos ε z ∂μ) - M0 * (∫ z, tentFn ε z ∂μ)
      = ∫ z, (f z * clampPos ε z - M0 * tentFn ε z) ∂μ := by
    rw [integral_sub hF (hT.const_mul M0), integral_const_mul]
  have e2 : (∫ z, f z * clampPos ε z ∂μ) + M0 * (∫ z, tentFn ε z ∂μ)
      = ∫ z, (f z * clampPos ε z + M0 * tentFn ε z) ∂μ := by
    rw [integral_add hF (hT.const_mul M0), integral_const_mul]
  constructor
  · rw [e1]
    refine integral_mono ((hF).sub (hT.const_mul M0)) hI (fun z => ?_)
    have := (abs_le.1 (key_bound hM0 hε z)).1
    dsimp only
    linarith
  · rw [e2]
    refine integral_mono hI ((hF).add (hT.const_mul M0)) (fun z => ?_)
    have := (abs_le.1 (key_bound hM0 hε z)).2
    dsimp only
    linarith

/-- The squeeze theorem: for a bounded continuous `f`, `∫ 1_{(0,∞)} f dν_N → ∫ 1_{(0,∞)} f dγ`
when `ν_N → γ = gaussianReal 0 w` (`w ≠ 0`) weakly. -/
theorem tendsto_indicator_integral {ν : ℕ → Measure ℝ} {w : ℝ≥0} (hw : w ≠ 0)
    (hP : ∀ N, IsProbabilityMeasure (ν N))
    (hconv : ∀ F : ℝ →ᵇ ℝ,
      Tendsto (fun N => ∫ x, F x ∂(ν N)) atTop (𝓝 (∫ x, F x ∂(gaussianReal 0 w))))
    {f : ℝ → ℝ} (hf : Continuous f) {M0 : ℝ} (hM0 : ∀ z, |f z| ≤ M0) :
    Tendsto (fun N => ∫ z, indicator (Ioi 0) f z ∂(ν N)) atTop
      (𝓝 (∫ z, indicator (Ioi 0) f z ∂(gaussianReal 0 w))) := by
  have hcl : gaussianReal 0 w {0} = 0 := (gaussianReal_absolutelyContinuous 0 hw) Real.volume_singleton
  have h0 : ∀ᵐ z ∂(gaussianReal 0 w), z ≠ 0 := by
    have hs : {z : ℝ | ¬ z ≠ 0} = {0} := by ext z; simp
    rw [ae_iff, hs]
    exact hcl
  have hTg := tendsto_tent_integral (γ := gaussianReal 0 w) h0
  have hCg := tendsto_clamp_integral (γ := gaussianReal 0 w) hf hM0
  rw [tendsto_order]
  constructor
  · intro a' ha'
    have hL := hCg.sub (hTg.const_mul M0)
    rw [mul_zero, sub_zero] at hL
    obtain ⟨ε, hε1, hε2⟩ := ((hL.eventually_const_lt ha').and self_mem_nhdsWithin).exists
    have hε : (0 : ℝ) < ε := hε2
    have hlo := (conv_bc hconv (fun z => f z * clampPos ε z) (hf.mul (continuous_clampPos ε)) M0
      (fun z => by
        show |f z * clampPos ε z| ≤ M0
        rw [abs_mul, abs_of_nonneg (clampPos_nonneg ε z)]
        nlinarith [hM0 z, clampPos_le_one ε z, clampPos_nonneg ε z, abs_nonneg (f z)])).sub
      ((conv_bc hconv (tentFn ε) (continuous_tentFn ε) 1 (fun z => by
        rw [abs_of_nonneg (tentFn_nonneg ε z)]
        exact tentFn_le_one hε z)).const_mul M0)
    filter_upwards [hlo.eventually_const_lt hε1] with N hN
    have := hP N
    exact lt_of_lt_of_le hN (bounds_N hf hM0 hε).1
  · intro b' hb'
    have hU := hCg.add (hTg.const_mul M0)
    rw [mul_zero, add_zero] at hU
    obtain ⟨ε, hε1, hε2⟩ := ((hU.eventually_lt_const hb').and self_mem_nhdsWithin).exists
    have hε : (0 : ℝ) < ε := hε2
    have hup := (conv_bc hconv (fun z => f z * clampPos ε z) (hf.mul (continuous_clampPos ε)) M0
      (fun z => by
        show |f z * clampPos ε z| ≤ M0
        rw [abs_mul, abs_of_nonneg (clampPos_nonneg ε z)]
        nlinarith [hM0 z, clampPos_le_one ε z, clampPos_nonneg ε z, abs_nonneg (f z)])).add
      ((conv_bc hconv (tentFn ε) (continuous_tentFn ε) 1 (fun z => by
        rw [abs_of_nonneg (tentFn_nonneg ε z)]
        exact tentFn_le_one hε z)).const_mul M0)
    filter_upwards [hup.eventually_lt_const hε1] with N hN
    have := hP N
    exact lt_of_le_of_lt (bounds_N hf hM0 hε).2 hN

/-! ### The Gaussian limit: mass of the positive half-line -/

theorem gauss_half {w : ℝ≥0} (hw : w ≠ 0) : gaussianReal 0 w (Ioi 0) = 2⁻¹ := by
  have hcl : gaussianReal 0 w {0} = 0 := (gaussianReal_absolutelyContinuous 0 hw) Real.volume_singleton
  have hsymm : gaussianReal 0 w (Iio 0) = gaussianReal 0 w (Ioi 0) := by
    have h1 : (gaussianReal 0 w).map (fun x => -x) (Ioi 0) = gaussianReal 0 w (Iio 0) := by
      rw [Measure.map_apply measurable_neg measurableSet_Ioi]
      congr 1
      ext x
      simp
    have h2 : (gaussianReal 0 w).map (fun x => -x) = gaussianReal 0 w := by
      rw [gaussianReal_map_neg, neg_zero]
    rw [← h1, h2]
  have hsum : gaussianReal 0 w (Iio 0) + gaussianReal 0 w (Ioi 0) = 1 := by
    have hdisj : Disjoint (Iio (0 : ℝ)) (Ioi 0) := Set.disjoint_left.2 (fun x (hx : x < 0) (hx' : 0 < x) => lt_asymm hx hx')
    rw [← measure_union hdisj measurableSet_Ioi,
      Set.Iio_union_Ioi, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), hcl]
    simp
  rw [hsymm, ← two_mul] at hsum
  have h2 : gaussianReal 0 w (Ioi 0) * 2 = 1 := by rw [mul_comm]; exact hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left h2

theorem tendsto_half {ν : ℕ → Measure ℝ} {w : ℝ≥0} (hw : w ≠ 0)
    (hP : ∀ N, IsProbabilityMeasure (ν N))
    (hconv : ∀ F : ℝ →ᵇ ℝ,
      Tendsto (fun N => ∫ x, F x ∂(ν N)) atTop (𝓝 (∫ x, F x ∂(gaussianReal 0 w)))) :
    Tendsto (fun N => (ν N (Ioi 0)).toReal) atTop (𝓝 (1 / 2)) := by
  have h := tendsto_indicator_integral hw hP hconv (f := fun _ => (1 : ℝ)) continuous_const
    (M0 := 1) (fun z => by simp)
  have hN : ∀ N, ∫ z, indicator (Ioi 0) (fun _ => (1 : ℝ)) z ∂(ν N) = (ν N (Ioi 0)).toReal := by
    intro N
    haveI := hP N
    rw [integral_indicator_const (1 : ℝ) measurableSet_Ioi, smul_eq_mul, mul_one, measureReal_def]
  have hG : ∫ z, indicator (Ioi 0) (fun _ => (1 : ℝ)) z ∂(gaussianReal 0 w) = 1 / 2 := by
    rw [integral_indicator_const (1 : ℝ) measurableSet_Ioi, smul_eq_mul, mul_one, measureReal_def,
      gauss_half hw]
    simp [ENNReal.toReal_inv]
  simp only [hN] at h
  rw [hG] at h
  exact h

/-! ### Conditioning -/

theorem cond_integral_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) {Z : X → ℝ}
    (hZ : Measurable Z) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f (Z x) ∂(cond μ {x | 0 < Z x}) =
      (μ {x | 0 < Z x}).toReal⁻¹ * ∫ z, indicator (Ioi 0) f z ∂(μ.map Z) := by
  have hA : MeasurableSet {x | 0 < Z x} := measurableSet_lt measurable_const hZ
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    ← integral_indicator hA]
  congr 1
  have h1 : ∀ x, {x | 0 < Z x}.indicator (fun x => f (Z x)) x = (Ioi 0).indicator f (Z x) := by
    intro x
    by_cases h : 0 < Z x
    · simp [h]
    · simp [h]
  simp_rw [h1]
  rw [integral_map hZ.aemeasurable (hf.indicator measurableSet_Ioi).aestronglyMeasurable]

/-- The half-normal density integral: `∫ f · halfNormalDensity v = 2 ∫_{(0,∞)} f dγ_v`. -/
theorem halfNormal_integral {v : ℝ} (hv : 0 < v) (f : ℝ → ℝ) :
    ∫ z, f z * halfNormalDensity v z = 2 * ∫ z, indicator (Ioi 0) f z ∂(gaussianReal 0 v.toNNReal) := by
  have hw : v.toNNReal ≠ 0 := (Real.toNNReal_pos.2 hv).ne'
  rw [integral_gaussianReal_eq_integral_smul hw, ← integral_const_mul]
  congr 1
  funext z
  have hvc : ((v.toNNReal : ℝ≥0) : ℝ) = v := Real.coe_toNNReal v hv.le
  have key : Real.sqrt (2 / (Real.pi * v)) = 2 * (Real.sqrt (2 * Real.pi * v))⁻¹ := by
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    have h1 : (2 : ℝ) / (Real.pi * v) = 4 / (2 * Real.pi * v) := by
      field_simp
      ring
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h1, Real.sqrt_div' _ (by positivity), h4, div_eq_mul_inv]
  by_cases hz : 0 < z
  · simp only [halfNormalDensity, if_pos hz, indicator_of_mem (show z ∈ Ioi 0 from hz),
      gaussianPDFReal, smul_eq_mul, hvc, sub_zero]
    rw [key]
    ring
  · simp only [halfNormalDensity, if_neg hz, indicator_of_notMem (show z ∉ Ioi 0 from hz),
      smul_eq_mul, mul_zero]

/-! ### Measurability of the statistic -/

theorem linCoord_measurable {d N : ℕ} {ρ ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    Measurable (linCoord (withDensityReal ρ) ψ : Config d N → ℝ) := by
  have hψm : Measurable ψ := hψ.measurable
  unfold linCoord
  fun_prop

/-! ### Assembly: (B1) and (B2) for the canonical Gibbs laws -/

/-- The law of the statistic `Z_{N+1}` under `P_{N+1,β}` (shifted by one so that the Gibbs measure is
a probability measure for every index, `HRS.MD.EQLawFlow.eqlaw_gibbs_prob`). -/
def shiftedLaw {d : ℕ} (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ ψ : Torus d → ℝ) (N : ℕ) :
    Measure ℝ :=
  law (canonicalGibbs (periodicRiesz d s) V (N + 1) β)
    (linCoord (withDensityReal ρ) ψ : Config d (N + 1) → ℝ)

/-- Packets B1 and B2 of Example 5.11 (`A:ex:conditioned`), assuming the centering clause `hCT` of
Theorem 2.9 and `v > 0`. -/
theorem cond_example_B {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ)
    (hCT : type_of% (@HRS.Main.centering_transition d))
    (hv : 0 < susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) :
    Tendsto (fun N => (canonicalGibbs (periodicRiesz d s) V N β
        {X | 0 < linCoord (withDensityReal ρ) ψ X}).toReal) atTop (𝓝 (1 / 2)) ∧
    ∀ f : ℝ → ℝ, Continuous f → (∃ M, ∀ z, |f z| ≤ M) →
      Tendsto (fun N => ∫ X, f (linCoord (withDensityReal ρ) ψ X)
          ∂(ProbabilityTheory.cond (canonicalGibbs (periodicRiesz d s) V N β)
            {X | 0 < linCoord (withDensityReal ρ) ψ X})) atTop
        (𝓝 (∫ z, f z * halfNormalDensity
          (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ) z)) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hψc : Continuous ψ := StaticLimitAux.continuous_of_smooth hψ
  have hconv := (hCT hd (s := s) hs0 hsd V hV β hβ ρ hρ ψ hψ).1 hs
  have hw : (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ).toNNReal ≠ 0 :=
    (Real.toNNReal_pos.2 hv).ne'
  have hP : ∀ N : ℕ, IsProbabilityMeasure (shiftedLaw s V β ρ ψ N) := fun N => by
    have : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (N + 1) β) :=
      HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
    unfold shiftedLaw law
    exact inferInstance
  have hconv' : ∀ F : ℝ →ᵇ ℝ, Tendsto (fun N => ∫ x, F x ∂(shiftedLaw s V β ρ ψ N)) atTop
      (𝓝 (∫ x, F x ∂(gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β ψ ψ).toNNReal))) :=
    fun F => (tendsto_add_atTop_iff_nat 1).2 (hconv F)
  -- (B1)
  have hB : Tendsto (fun N => (shiftedLaw s V β ρ ψ N (Ioi 0)).toReal) atTop (𝓝 (1 / 2)) :=
    tendsto_half hw hP hconv'
  have hBA : ∀ N : ℕ, (shiftedLaw s V β ρ ψ N (Ioi 0)).toReal =
      (canonicalGibbs (periodicRiesz d s) V (N + 1) β
        {X | 0 < linCoord (withDensityReal ρ) ψ X}).toReal := fun N => by
    unfold shiftedLaw law
    rw [Measure.map_apply (linCoord_measurable (ρ := ρ) (N := N + 1) hψc) measurableSet_Ioi]
    rfl
  simp only [hBA] at hB
  refine ⟨(tendsto_add_atTop_iff_nat 1).1 hB, fun f hf hfb => ?_⟩
  obtain ⟨M, hM⟩ := hfb
  have hI := tendsto_indicator_integral hw hP hconv' hf hM
  have hinv : Tendsto (fun N => (canonicalGibbs (periodicRiesz d s) V (N + 1) β
      {X | 0 < linCoord (withDensityReal ρ) ψ X}).toReal⁻¹) atTop (𝓝 ((1 / 2 : ℝ)⁻¹)) :=
    hB.inv₀ (by norm_num) |> fun h => by simpa only [hBA] using h
  have hprod := hinv.mul hI
  have hcond : ∀ N : ℕ, ∫ X, f (linCoord (withDensityReal ρ) ψ X)
      ∂(ProbabilityTheory.cond (canonicalGibbs (periodicRiesz d s) V (N + 1) β)
        {X | 0 < linCoord (withDensityReal ρ) ψ X}) =
      (canonicalGibbs (periodicRiesz d s) V (N + 1) β
        {X | 0 < linCoord (withDensityReal ρ) ψ X}).toReal⁻¹ *
        ∫ z, indicator (Ioi 0) f z ∂(shiftedLaw s V β ρ ψ N) := fun N =>
    cond_integral_eq (canonicalGibbs (periodicRiesz d s) V (N + 1) β)
      (linCoord_measurable (ρ := ρ) (N := N + 1) hψc) hf.measurable
  have e : ((1 / 2 : ℝ))⁻¹ = 2 := by norm_num
  rw [e] at hprod
  rw [halfNormal_integral hv f]
  refine (tendsto_add_atTop_iff_nat 1).1 ?_
  simp only [hcond]
  exact hprod

end HRS.ME.CondExample

end
