import Mathlib
import HRS.Prob.Metrics
import HRS.Main.MeanPartMetric

/-!
# Mean-particle packet: convergence in distribution from `W_1 → 0`, and a lower-tail estimate

* `mp_tendstoInDistribution_of_wE1` : `W_1(law X_i, law Z) → 0` implies `X_i ⇒ Z` in distribution;
* `mp_lowerTail` : if `W_1(law ξ_i, law ζ) → 0` and `δ_i → +∞`, then `P_i(ξ_i + δ_i ≤ M) → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

section MPConv

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {Ω' : Type*} [MeasurableSpace Ω']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **`W_1 → 0` implies convergence in distribution.** If `X i` and `Z` are a.e. measurable and
`W_1(law (X i), law Z) → 0` along `l`, then `X i` converges to `Z` in distribution. -/
theorem mp_tendstoInDistribution_of_wE1 [l.IsCountablyGenerated] (X : ∀ i, Ω i → E) (Z : Ω' → E)
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (hX : ∀ i, AEMeasurable (X i) (P i)) (hZ : AEMeasurable Z P')
    (hW : Tendsto (fun i => wassersteinE 1 (law (P i) (X i)) (law P' Z)) l (𝓝 0)) :
    TendstoInDistribution X l Z P P' := by
  refine ⟨hX, hZ, ?_⟩
  refine (tendsto_iff_forall_lipschitz_integral_tendsto (F := l)).2 ?_
  rintro f ⟨C, hC⟩ ⟨L, hL⟩
  simp only [ProbabilityMeasure.coe_mk]
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  have hev : ∀ᶠ i in l, wassersteinE 1 (law (P i) (X i)) (law P' Z) < 1 :=
    hW.eventually (gt_mem_nhds zero_lt_one)
  have hT : Tendsto (fun i => (L : ℝ) * (wassersteinE 1 (law (P i) (X i)) (law P' Z)).toReal) l
      (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW).const_mul (L : ℝ)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) (hev.mono fun i hi => ?_) hT
  rw [Real.dist_eq]
  exact mp_abs_integral_sub_le_wE1 hL ⟨C, hC⟩ _ _ hi.ne_top

end MPConv

section MPTail

/-- Half-line comparison for two probability measures on `ℝ` with finite `W_1`:
`μ(-∞, a] ≤ ν(-∞, b] + W_1(μ, ν)` whenever `a + 1 ≤ b` (via a 1-Lipschitz cutoff). -/
theorem mp_real_Iic_le_of_wE1 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hW : wassersteinE 1 μ ν ≠ ⊤) (a b : ℝ) (hab : a + 1 ≤ b) :
    μ.real (Set.Iic a) ≤ ν.real (Set.Iic b) + (wassersteinE 1 μ ν).toReal := by
  set g : ℝ → ℝ := fun x => max 0 (min 1 (b - x)) with hg
  have hsub : LipschitzWith 1 (fun x : ℝ => b - x) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq,
      show b - x - (b - y) = -(x - y) by ring, abs_neg]
  have hL : LipschitzWith 1 g := (hsub.const_min 1).const_max 0
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := fun x => by
    refine ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hb : ∃ C : ℝ, ∀ x y, dist (g x) (g y) ≤ C := ⟨1, fun x y => by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hg01 x, hg01 y]⟩
  have hgi : ∀ m : Measure ℝ, IsProbabilityMeasure m → Integrable g m := fun m hm =>
    Integrable.of_bound hL.continuous.aestronglyMeasurable 1
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hg01 x])
  have h1 : μ.real (Set.Iic a) ≤ ∫ x, g x ∂μ := by
    rw [← integral_indicator_one (measurableSet_Iic (a := a)) (μ := μ)]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) (hgi μ inferInstance)
      fun x => ?_
    by_cases hx : x ≤ a
    · have : g x = 1 := by
        simp only [hg]
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      simp [Set.indicator, hx, this]
    · simp [Set.indicator, hx, (hg01 x).1]
  have h2 : ∫ x, g x ∂ν ≤ ν.real (Set.Iic b) := by
    rw [← integral_indicator_one (measurableSet_Iic (a := b)) (μ := ν)]
    refine integral_mono (hgi ν inferInstance)
      ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) fun x => ?_
    by_cases hx : x ≤ b
    · simp [Set.indicator, hx, (hg01 x).2]
    · have : g x = 0 := by
        simp only [hg]
        rw [min_eq_right (by linarith [not_le.1 hx]), max_eq_left (by linarith [not_le.1 hx])]
      simp [Set.indicator, hx, this]
  have h3 := mp_abs_integral_sub_le_wE1 hL hb μ ν hW
  have h4 := (abs_le.1 h3).2
  simp only [NNReal.coe_one, one_mul] at h4
  linarith

/-- **Lower-tail estimate.** Let `ξ_i` be real random variables on `(Ω_i, P_i)` and `ζ` a real
random variable on `(Ω', P')` with `W_1(law ξ_i, law ζ) → 0` along `l`, and let `δ_i → +∞`
(deterministic). Then for every `M`, `P_i(ξ_i + δ_i ≤ M) → 0`. -/
theorem mp_lowerTail {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {Ω' : Type*} [MeasurableSpace Ω']
    (P : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (P i)] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (ξ : ∀ i, Ω i → ℝ) (ζ : Ω' → ℝ)
    (hξ : ∀ i, AEMeasurable (ξ i) (P i)) (hζ : AEMeasurable ζ P') (δ : ι → ℝ)
    (hW : Tendsto (fun i => wassersteinE 1 (law (P i) (ξ i)) (law P' ζ)) l (𝓝 0))
    (hδ : Tendsto δ l atTop) (M : ℝ) :
    Tendsto (fun i => P i {ω | ξ i ω + δ i ≤ M}) l (𝓝 0) := by
  have hmeas : ∀ i, (P i) {ω | ξ i ω + δ i ≤ M} = (law (P i) (ξ i)) (Set.Iic (M - δ i)) := by
    intro i
    rw [Measure.map_apply_of_aemeasurable (hξ i) measurableSet_Iic]
    congr 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  simp_rw [hmeas]
  rw [← ENNReal.tendsto_toReal_iff (fun i => measure_ne_top _ _) ENNReal.zero_ne_top]
  have hν : IsProbabilityMeasure (law P' ζ) := inferInstance
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨b, hb⟩ := eventually_atBot.1
    ((ProbabilityTheory.tendsto_cdf_atBot (law P' ζ)).eventually (gt_mem_nhds (half_pos hε)))
  have hbb : (law P' ζ).real (Set.Iic b) < ε / 2 := by
    rw [← ProbabilityTheory.cdf_eq_real]; exact hb b le_rfl
  have hev1 : ∀ᶠ i in l, wassersteinE 1 (law (P i) (ξ i)) (law P' ζ) < ENNReal.ofReal (ε / 2) :=
    hW.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))
  have hev2 : ∀ᶠ i in l, M - b + 1 ≤ δ i := hδ.eventually_ge_atTop _
  filter_upwards [hev1, hev2] with i h1 h2
  have hfin : wassersteinE 1 (law (P i) (ξ i)) (law P' ζ) ≠ ⊤ := h1.ne_top
  have hW2 : (wassersteinE 1 (law (P i) (ξ i)) (law P' ζ)).toReal < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal h1
  have key := mp_real_Iic_le_of_wE1 (law (P i) (ξ i)) (law P' ζ) hfin (M - δ i) b
    (by linarith)
  rw [Real.dist_eq, ENNReal.toReal_zero, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  have : ((law (P i) (ξ i)) (Set.Iic (M - δ i))).toReal =
      (law (P i) (ξ i)).real (Set.Iic (M - δ i)) := rfl
  rw [this]
  linarith

end MPTail

end HRS
