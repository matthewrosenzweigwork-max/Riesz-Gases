import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs
import HRS.ME.CondExample

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- Pointwise squeeze on `E`. -/
theorem p_cp6_key {E : Type*} [TopologicalSpace E] (g : E →ᵇ ℝ) (a : E → ℝ) {ε : ℝ} (hε : 0 < ε) (x : E) :
    |Set.indicator {x | 0 < a x} (fun x => g x) x - g x * HRS.ME.CondExample.clampPos ε (a x)|
      ≤ ‖g‖ * HRS.ME.CondExample.tentFn ε (a x) := by
  have h := HRS.ME.CondExample.key_bound (f := fun _ => g x) (M0 := ‖g‖)
    (fun _ => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x) hε (a x)
  by_cases hx : 0 < a x
  · simpa [Set.indicator_of_mem (show x ∈ {x | 0 < a x} from hx),
      Set.indicator_of_mem (show a x ∈ Set.Ioi (0 : ℝ) from hx)] using h
  · simpa [Set.indicator_of_notMem (show x ∉ {x | 0 < a x} from hx),
      Set.indicator_of_notMem (show a x ∉ Set.Ioi (0 : ℝ) from hx)] using h

theorem p_cp6_int_I {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (g : E →ᵇ ℝ) (a : E → ℝ) (ha : Continuous a) :
    Integrable (Set.indicator {x | 0 < a x} (fun x => g x)) μ :=
  (g.integrable μ).indicator (isOpen_lt continuous_const ha).measurableSet

theorem p_cp6_int_C {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (g : E →ᵇ ℝ) (a : E → ℝ) (ha : Continuous a) (ε : ℝ) :
    Integrable (fun x => g x * HRS.ME.CondExample.clampPos ε (a x)) μ := by
  refine Integrable.mono' (g.integrable μ).norm
    ((g.continuous.mul ((HRS.ME.CondExample.continuous_clampPos ε).comp ha)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have h0 := HRS.ME.CondExample.clampPos_nonneg ε (a x)
  have h1 := HRS.ME.CondExample.clampPos_le_one ε (a x)
  rw [Real.norm_eq_abs (HRS.ME.CondExample.clampPos ε (a x)), abs_of_nonneg h0]
  nlinarith [norm_nonneg (g x)]

theorem p_cp6_int_T {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (a : E → ℝ) (ha : Continuous a) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => HRS.ME.CondExample.tentFn ε (a x)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((HRS.ME.CondExample.continuous_tentFn ε).comp ha).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (HRS.ME.CondExample.tentFn_nonneg ε (a x))]
  exact HRS.ME.CondExample.tentFn_le_one hε (a x)

theorem p_cp6_diff {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (g : E →ᵇ ℝ) (a : E → ℝ) (ha : Continuous a)
    {ε : ℝ} (hε : 0 < ε) :
    |(∫ x, Set.indicator {x | 0 < a x} (fun x => g x) x ∂μ)
        - ∫ x, g x * HRS.ME.CondExample.clampPos ε (a x) ∂μ|
      ≤ ‖g‖ * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂μ := by
  rw [← integral_sub (p_cp6_int_I μ g a ha) (p_cp6_int_C μ g a ha ε), ← integral_const_mul,
    ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le ((p_cp6_int_T μ a ha hε).const_mul _)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact p_cp6_key g a hε x)

theorem p_cp6_tent_null {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (γ : Measure E) [IsFiniteMeasure γ] (a : E → ℝ) (ha : Continuous a)
    (hnull : γ {x | a x = 0} = 0) :
    Tendsto (fun ε => ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ) (𝓝[>] 0) (𝓝 0) := by
  have key := tendsto_integral_filter_of_dominated_convergence (μ := γ) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε x => HRS.ME.CondExample.tentFn ε (a x)) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const (1 : ℝ)) ?_
  · simpa using key
  · exact Filter.Eventually.of_forall fun ε =>
      ((HRS.ME.CondExample.continuous_tentFn ε).comp ha).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine ae_of_all _ fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (HRS.ME.CondExample.tentFn_nonneg _ _)]
    exact HRS.ME.CondExample.tentFn_le_one hε _
  · have h0 : ∀ᵐ x ∂γ, a x ≠ 0 := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [h0] with x hx
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), HRS.ME.CondExample.tentFn ε (a x) = 0 := by
      filter_upwards [Ioo_mem_nhdsGT (abs_pos.2 hx)] with ε hε
      have h1 : 1 ≤ |a x| / ε := (one_le_div hε.1).2 hε.2.le
      unfold HRS.ME.CondExample.tentFn
      rw [max_eq_left (by linarith)]
    exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)

/-- **P6** (statement copied from the spec). -/
theorem condou_tendsto_indicator2 {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (ν : ℕ → Measure E) [∀ n, IsProbabilityMeasure (ν n)] (γ : Measure E) [IsProbabilityMeasure γ]
    (a : E → ℝ) (ha : Continuous a) (hnull : γ {x | a x = 0} = 0)
    (hconv : ConvergesInLaw ν γ) (g : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, Set.indicator {x | 0 < a x} (fun x => g x) x ∂ν n) atTop
      (𝓝 (∫ x, Set.indicator {x | 0 < a x} (fun x => g x) x ∂γ)) := by
  have hT := p_cp6_tent_null γ a ha hnull
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hM : 0 ≤ ‖g‖ := norm_nonneg g
  have hpos : 0 < ‖g‖ + 1 := by linarith
  -- choose ε
  obtain ⟨ε, hεT, hε⟩ := ((hT.eventually (gt_mem_nhds (show (0 : ℝ) < δ / (4 * (‖g‖ + 1)) by positivity))).and
    self_mem_nhdsWithin).exists
  have hε0 : 0 < ε := hε
  have hTγ : ‖g‖ * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ < δ / 4 := by
    have h1 : ‖g‖ * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ
        ≤ (‖g‖ + 1) * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ :=
      mul_le_mul_of_nonneg_right (by linarith)
        (integral_nonneg fun x => HRS.ME.CondExample.tentFn_nonneg _ _)
    have h2 : (‖g‖ + 1) * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ
        < (‖g‖ + 1) * (δ / (4 * (‖g‖ + 1))) := mul_lt_mul_of_pos_left hεT hpos
    have h3 : (‖g‖ + 1) * (δ / (4 * (‖g‖ + 1))) = δ / 4 := by field_simp
    linarith
  -- bounded continuous test functions
  let C : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => g x * HRS.ME.CondExample.clampPos ε (a x))
    (g.continuous.mul ((HRS.ME.CondExample.continuous_clampPos ε).comp ha)) ‖g‖ (fun x => by
      rw [norm_mul]
      have h0 := HRS.ME.CondExample.clampPos_nonneg ε (a x)
      have h1 := HRS.ME.CondExample.clampPos_le_one ε (a x)
      rw [Real.norm_eq_abs (HRS.ME.CondExample.clampPos ε (a x)), abs_of_nonneg h0]
      nlinarith [norm_nonneg (g x), g.norm_coe_le_norm x])
  let T : E →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => HRS.ME.CondExample.tentFn ε (a x))
    ((HRS.ME.CondExample.continuous_tentFn ε).comp ha) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (HRS.ME.CondExample.tentFn_nonneg ε (a x))]
      exact HRS.ME.CondExample.tentFn_le_one hε0 (a x))
  have hCc := hconv C
  have hTc := hconv T
  rw [Metric.tendsto_atTop] at hCc hTc
  obtain ⟨N1, hN1⟩ := hCc (δ / 4) (by positivity)
  obtain ⟨N2, hN2⟩ := hTc (δ / (4 * (‖g‖ + 1))) (by positivity)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have e1 := hN1 n (le_trans (le_max_left _ _) hn)
  have e2 := hN2 n (le_trans (le_max_right _ _) hn)
  have hCn : ∫ x, C x ∂(ν n) = ∫ x, g x * HRS.ME.CondExample.clampPos ε (a x) ∂(ν n) := rfl
  have hCg : ∫ x, C x ∂γ = ∫ x, g x * HRS.ME.CondExample.clampPos ε (a x) ∂γ := rfl
  have hTn : ∫ x, T x ∂(ν n) = ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂(ν n) := rfl
  have hTg : ∫ x, T x ∂γ = ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ := rfl
  rw [hCn, hCg, Real.dist_eq] at e1
  rw [hTn, hTg, Real.dist_eq] at e2
  have d1 := p_cp6_diff (ν n) g a ha hε0
  have d2 := p_cp6_diff γ g a ha hε0
  have hb : ‖g‖ * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂(ν n)
      < ‖g‖ * ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ + δ / 4 := by
    have h1 : ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂(ν n)
        - ∫ x, HRS.ME.CondExample.tentFn ε (a x) ∂γ ≤ δ / (4 * (‖g‖ + 1)) := by
      have := (abs_lt.1 e2).2; linarith
    have hη : 0 < δ / (4 * (‖g‖ + 1)) := by positivity
    have h3 : (‖g‖ + 1) * (δ / (4 * (‖g‖ + 1))) = δ / 4 := by field_simp
    have h2 := mul_le_mul_of_nonneg_left h1 hM
    nlinarith
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at e1
  rw [abs_le] at d1 d2
  constructor <;> nlinarith [e1.1, e1.2, d1.1, d1.2, d2.1, d2.2]

end HRS.MH.CondOuPackets
