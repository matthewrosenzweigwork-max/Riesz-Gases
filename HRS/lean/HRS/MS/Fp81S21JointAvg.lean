import HRS.MS.Fp81S21RankKernel3
import HRS.Main.Headline

/-!
# S2.1(iii), packet 32c: a generic joint averaging upgrade

This file isolates the abstract step from a joint comparison of two time-
integrated coordinates to a comparison in which the first coordinate is a
continuous path.  A common bounded linear averaging map acts on the first
coordinate, while the second (quadratic) coordinate is retained unchanged.
The two continuous versions are assumed to have mean-square smoothing errors
under their respective laws.  No physical trajectory or realization data enter.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

private theorem fp81s21_jointAvg_sqErr_wasserstein
    {Ω B : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (f g : Ω → B) (hf : Measurable f) (hg : Measurable g)
    (ε : ℝ) (hε : 0 ≤ ε)
    (herr : fp81s21_SqErr P f g ε) :
    wassersteinE 2 (law P f) (law P g) ≤ ENNReal.ofReal ε := by
  have hcouple := wassersteinE_le_of_coupling P 2 (by norm_num) f g
    hf.aemeasurable hg.aemeasurable
  have hcost : ∫⁻ ω, ENNReal.ofReal (‖f ω - g ω‖ ^ 2) ∂P ≤
      ENNReal.ofReal (ε ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal herr.1
      (ae_of_all P fun ω => sq_nonneg (‖f ω - g ω‖))]
    exact ENNReal.ofReal_le_ofReal herr.2
  have hpow : ∫⁻ ω, ENNReal.ofReal (‖f ω - g ω‖ ^ ((2 : ℕ) : ℝ)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (‖f ω - g ω‖ ^ 2) ∂P := by
    apply lintegral_congr
    intro ω
    congr 1
    rw [Real.rpow_natCast]
  calc
    wassersteinE 2 (law P f) (law P g) ≤
        (∫⁻ ω, ENNReal.ofReal (‖f ω - g ω‖ ^ ((2 : ℕ) : ℝ)) ∂P) ^
          (1 / (2 : ℝ)) := hcouple
    _ = (∫⁻ ω, ENNReal.ofReal (‖f ω - g ω‖ ^ 2) ∂P) ^ (1 / (2 : ℝ)) := by
      rw [hpow]
    _ ≤ (ENNReal.ofReal (ε ^ 2)) ^ (1 / (2 : ℝ)) :=
      ENNReal.rpow_le_rpow hcost (by norm_num)
    _ = ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg ε)
        (by norm_num : 0 ≤ (1 / (2 : ℝ)))]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_nonneg hε]

/-- The operator which averages the linear coordinate and leaves the quadratic
time-
`L²` coordinate untouched has norm at most `max 1 ‖S‖` for the product
sup norms. -/
private theorem fp81s21_jointAvg_prodMap_norm
    {U C : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    (S : U →L[ℝ] C) :
    ‖S.prodMap (ContinuousLinearMap.id ℝ U)‖ ≤ max 1 ‖S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rcases z with ⟨u, v⟩
  change max ‖S u‖ ‖v‖ ≤ max 1 ‖S‖ * max ‖u‖ ‖v‖
  apply max_le
  · have hK : 0 ≤ max 1 ‖S‖ := le_trans (by norm_num) (le_max_left 1 ‖S‖)
    calc
      ‖S u‖ ≤ ‖S‖ * ‖u‖ := S.le_opNorm u
      _ ≤ max 1 ‖S‖ * ‖u‖ :=
        mul_le_mul_of_nonneg_right (le_max_right 1 ‖S‖) (norm_nonneg u)
      _ ≤ max 1 ‖S‖ * max ‖u‖ ‖v‖ :=
        mul_le_mul_of_nonneg_left (le_max_left ‖u‖ ‖v‖) hK
  · have hz : 0 ≤ max ‖u‖ ‖v‖ := le_trans (norm_nonneg u) (le_max_left _ _)
    calc
      ‖v‖ ≤ max ‖u‖ ‖v‖ := le_max_right _ _
      _ = 1 * max ‖u‖ ‖v‖ := (one_mul _).symm
      _ ≤ max 1 ‖S‖ * max ‖u‖ ‖v‖ :=
        mul_le_mul_of_nonneg_right (le_max_left 1 ‖S‖) hz

/-- Generic joint `W₂` averaging estimate.  `U` is the time-`L²` space and
`C` the continuous-path space.  The source laws compare `(f,b)` jointly.  The
same averaging map `S` is applied to each first coordinate, and the second
coordinate `b` remains part of the output coupling.  The `SqErr` hypotheses
are the two law-specific continuous-version smoothing errors.

The factor `max 1 ‖S‖` is the operator norm bound for the joint map
`(u,b) ↦ (S u,b)`. -/
theorem fp81s21_jointAvg_wasserstein
    {Ω₁ Ω₂ U C : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [MeasurableSpace U] [BorelSpace U]
    [SecondCountableTopology U] [CompleteSpace U]
    [NormedAddCommGroup C] [NormedSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
    [SecondCountableTopology C] [CompleteSpace C]
    (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (f₁ b₁ : Ω₁ → U) (f₂ b₂ : Ω₂ → U)
    (x₁ : Ω₁ → C) (x₂ : Ω₂ → C)
    (S : U →L[ℝ] C)
    (hf₁ : Measurable f₁) (hb₁ : Measurable b₁) (hx₁ : Measurable x₁)
    (hf₂ : Measurable f₂) (hb₂ : Measurable b₂) (hx₂ : Measurable x₂)
    (ε q : ℝ) (hε : 0 ≤ ε) (hq : 0 ≤ q)
    (hsource : wassersteinE 2
      (law P₁ (fun ω => (f₁ ω, b₁ ω)))
      (law P₂ (fun ω => (f₂ ω, b₂ ω))) ≤ ENNReal.ofReal q)
    (herr₁ : fp81s21_SqErr P₁ x₁ (fun ω => S (f₁ ω)) ε)
    (herr₂ : fp81s21_SqErr P₂ x₂ (fun ω => S (f₂ ω)) ε) :
    wassersteinE 2
      (law P₁ (fun ω => (x₁ ω, b₁ ω)))
      (law P₂ (fun ω => (x₂ ω, b₂ ω))) ≤
        ENNReal.ofReal (2 * ε + max 1 ‖S‖ * q) := by
  let T : (U × U) →L[ℝ] (C × U) := S.prodMap (ContinuousLinearMap.id ℝ U)
  let source₁ : Ω₁ → U × U := fun ω => (f₁ ω, b₁ ω)
  let source₂ : Ω₂ → U × U := fun ω => (f₂ ω, b₂ ω)
  let actual₁ : Ω₁ → C × U := fun ω => (x₁ ω, b₁ ω)
  let actual₂ : Ω₂ → C × U := fun ω => (x₂ ω, b₂ ω)
  let approx₁ : Ω₁ → C × U := fun ω => (S (f₁ ω), b₁ ω)
  let approx₂ : Ω₂ → C × U := fun ω => (S (f₂ ω), b₂ ω)
  have hsource₁ : Measurable source₁ := hf₁.prodMk hb₁
  have hsource₂ : Measurable source₂ := hf₂.prodMk hb₂
  have hactual₁ : Measurable actual₁ := hx₁.prodMk hb₁
  have hactual₂ : Measurable actual₂ := hx₂.prodMk hb₂
  have happ₁ : Measurable approx₁ := (S.continuous.measurable.comp hf₁).prodMk hb₁
  have happ₂ : Measurable approx₂ := (S.continuous.measurable.comp hf₂).prodMk hb₂
  letI : IsProbabilityMeasure (law P₁ source₁) :=
    (Measure.isProbabilityMeasure_map_iff hsource₁.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law P₂ source₂) :=
    (Measure.isProbabilityMeasure_map_iff hsource₂.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law P₁ actual₁) :=
    (Measure.isProbabilityMeasure_map_iff hactual₁.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law P₂ actual₂) :=
    (Measure.isProbabilityMeasure_map_iff hactual₂.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law P₁ approx₁) :=
    (Measure.isProbabilityMeasure_map_iff happ₁.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (law P₂ approx₂) :=
    (Measure.isProbabilityMeasure_map_iff happ₂.aemeasurable).2 inferInstance
  have hmap₁ : law P₁ approx₁ = (law P₁ source₁).map T := by
    unfold law
    exact (AEMeasurable.map_map_of_aemeasurable T.continuous.measurable.aemeasurable
      hsource₁.aemeasurable).symm
  have hmap₂ : law P₂ approx₂ = (law P₂ source₂).map T := by
    unfold law
    exact (AEMeasurable.map_map_of_aemeasurable T.continuous.measurable.aemeasurable
      hsource₂.aemeasurable).symm
  have hTnorm : ‖T‖ ≤ max 1 ‖S‖ := by
    simpa [T] using fp81s21_jointAvg_prodMap_norm S
  have hmid : wassersteinE 2 (law P₁ approx₁) (law P₂ approx₂) ≤
      ENNReal.ofReal (max 1 ‖S‖ * q) := by
    rw [hmap₁, hmap₂]
    calc
      wassersteinE 2 ((law P₁ source₁).map T) ((law P₂ source₂).map T) ≤
          ENNReal.ofReal ‖T‖ * wassersteinE 2 (law P₁ source₁) (law P₂ source₂) :=
        HRS.Main.wassersteinE_map_clm_le T 2 (by norm_num) _ _
      _ ≤ ENNReal.ofReal ‖T‖ * ENNReal.ofReal q :=
        mul_le_mul_of_nonneg_left (by simpa [source₁, source₂] using hsource)
          (by positivity)
      _ = ENNReal.ofReal (‖T‖ * q) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (max 1 ‖S‖ * q) := by
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hTnorm hq)
  have hpair₁ : fp81s21_SqErr P₁ actual₁ approx₁ ε := by
    constructor
    · simpa [actual₁, approx₁, Prod.norm_def] using herr₁.1
    · simpa [actual₁, approx₁, Prod.norm_def] using herr₁.2
  have hpair₂rev : fp81s21_SqErr P₂ approx₂ actual₂ ε := by
    constructor
    · simpa [actual₂, approx₂, Prod.norm_def, norm_sub_rev] using herr₂.1
    · simpa [actual₂, approx₂, Prod.norm_def, norm_sub_rev] using herr₂.2
  have herrW₁ := fp81s21_jointAvg_sqErr_wasserstein actual₁ approx₁ hactual₁ happ₁ ε hε hpair₁
  have herrW₂ := fp81s21_jointAvg_sqErr_wasserstein approx₂ actual₂ happ₂ hactual₂ ε hε hpair₂rev
  have htri₁ := wassersteinE_triangle 2 (by norm_num)
    (law P₁ actual₁) (law P₁ approx₁) (law P₂ actual₂)
  have htri₂ := wassersteinE_triangle 2 (by norm_num)
    (law P₁ approx₁) (law P₂ approx₂) (law P₂ actual₂)
  have hsum : wassersteinE 2 (law P₁ actual₁) (law P₂ actual₂) ≤
      ENNReal.ofReal ε + (ENNReal.ofReal (max 1 ‖S‖ * q) + ENNReal.ofReal ε) := by
    calc
      wassersteinE 2 (law P₁ actual₁) (law P₂ actual₂) ≤
          wassersteinE 2 (law P₁ actual₁) (law P₁ approx₁) +
            wassersteinE 2 (law P₁ approx₁) (law P₂ actual₂) := htri₁
      _ ≤ ENNReal.ofReal ε +
          (wassersteinE 2 (law P₁ approx₁) (law P₂ approx₂) +
            wassersteinE 2 (law P₂ approx₂) (law P₂ actual₂)) := by
        exact add_le_add herrW₁ htri₂
      _ ≤ ENNReal.ofReal ε +
          (ENNReal.ofReal (max 1 ‖S‖ * q) + ENNReal.ofReal ε) := by
        exact add_le_add le_rfl (add_le_add hmid herrW₂)
  calc
    wassersteinE 2 (law P₁ actual₁) (law P₂ actual₂) ≤
        ENNReal.ofReal ε + (ENNReal.ofReal (max 1 ‖S‖ * q) + ENNReal.ofReal ε) := hsum
    _ = ENNReal.ofReal (2 * ε + max 1 ‖S‖ * q) := by
      rw [← ENNReal.ofReal_add (mul_nonneg (by positivity) hq) hε,
        ← ENNReal.ofReal_add hε (add_nonneg (mul_nonneg (by positivity) hq) hε)]
      congr 1
      ring

/-- Abstract fixed-then-vanishing-smoothing principle.  If for every smoothing
index `k` the target joint `W₂` distance is bounded by
`2 * ω k + K k * q n`, where `q n → 0`, `ω k → 0`, and all profiles are
nonnegative, then the target joint distance tends to zero.  The output profile
is its real-valued Wasserstein distance, which is finite by any one fixed
smoothing estimate. -/
theorem fp81s21_jointAvg_tendsto
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    (μ ν : ℕ → Measure B)
    (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hqt : Tendsto q atTop (𝓝 0))
    (ω K : ℕ → ℝ) (hω : ∀ k, 0 ≤ ω k) (hKt : ∀ k, 0 ≤ K k)
    (hωt : Tendsto ω atTop (𝓝 0))
    (hbound : ∀ k n, wassersteinE 2 (μ n) (ν n) ≤
      ENNReal.ofReal (2 * ω k + K k * q n)) :
    ∃ e : ℕ → ℝ,
      (∀ n, 0 ≤ e n) ∧ Tendsto e atTop (𝓝 0) ∧
      ∀ n, wassersteinE 2 (μ n) (ν n) ≤ ENNReal.ofReal (e n) := by
  let W : ℕ → ℝ≥0∞ := fun n => wassersteinE 2 (μ n) (ν n)
  have hWlim : Tendsto W atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.2
    intro δ hδ
    by_cases htop : δ = ⊤
    · simpa [htop]
    · have hδr : 0 < δ.toReal := ENNReal.toReal_pos hδ.ne' htop
      have hωevent : ∀ᶠ k in atTop, ω k < δ.toReal / 4 :=
        hωt.eventually (Iio_mem_nhds (by positivity))
      obtain ⟨k₀, hk₀⟩ := hωevent.exists
      have hprodlim : Tendsto (fun n => K k₀ * q n) atTop (𝓝 0) :=
        by simpa using (tendsto_const_nhds (x := K k₀)).mul hqt
      have hqevent : ∀ᶠ n in atTop, K k₀ * q n < δ.toReal / 2 :=
        hprodlim.eventually (Iio_mem_nhds (by positivity))
      filter_upwards [hqevent] with n hn
      have hreal : 2 * ω k₀ + K k₀ * q n ≤ δ.toReal := by
        nlinarith [hk₀, hn]
      have hW := hbound k₀ n
      calc
        W n ≤ ENNReal.ofReal (2 * ω k₀ + K k₀ * q n) := hW
        _ ≤ ENNReal.ofReal δ.toReal := ENNReal.ofReal_le_ofReal hreal
        _ = δ := ENNReal.ofReal_toReal htop
  have hfinite : ∀ n, W n ≠ ⊤ := by
    intro n
    have hlt : W n < ⊤ := lt_of_le_of_lt (hbound 0 n) ENNReal.ofReal_lt_top
    exact ne_of_lt hlt
  refine ⟨fun n => (W n).toReal, ?_, ?_, ?_⟩
  · intro n
    exact ENNReal.toReal_nonneg
  · exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hWlim
  · intro n
    change W n ≤ ENNReal.ofReal ((W n).toReal)
    rw [ENNReal.ofReal_toReal (hfinite n)]

/-! ## Exported axiom audit -/

#print axioms fp81s21_jointAvg_wasserstein
#print axioms fp81s21_jointAvg_tendsto

end HRS.Fp81.S21

end
