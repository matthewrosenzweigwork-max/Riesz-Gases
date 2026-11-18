import HRS.MS.R26T8AP11pu

/-!
# S8.2 nonlocal layer: the sum of the annular pieces is the local Riesz integral (P11e, part 1)
`r26t8a_loc_partition`: `HasSum (n ↦ locV (2^-n) X z) (∫ ‖z-v‖^(α-d) chi v F(Y+v,Y) dv)` for `z != 0`, `F` conormal of order `σ < d`
(dominated convergence with the dominator of `r26t8a_loc_integrable`, `sum_n |a_n| <= 2`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_loc_partition (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F → ∀ X z : Euc d, z ≠ 0 →
      HasSum (fun n : ℕ => r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F X z)
        (∫ v : Euc d, ‖z - v‖ ^ (alpha - (d : ℝ)) *
          (chi v * F (X + (-(1 / 2 : ℝ)) • z + v) (X + (-(1 / 2 : ℝ)) • z))) := by
  intro A hA F hF X z hz
  set Y : Euc d := X + (-(1 / 2 : ℝ)) • z with hY
  set e : ℝ := alpha - (d : ℝ) with he
  have hGi := r26t8a_loc_integrable d hd k b alpha M sigma halpha had hM hsd A hA F hF Y z hz
  set G : Euc d → ℝ := fun v => ‖z - v‖ ^ e * (closedBall (0 : Euc d) 2).indicator (fun v => ‖F (Y + v) Y‖) v
    with hG
  -- the terms
  set Fn : ℕ → Euc d → ℝ := fun n v => ‖z - v‖ ^ e *
    (r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v * F (Y + v) Y) with hFn
  have hR : ∀ n : ℕ, 0 < ((1 : ℝ) / 2) ^ n := fun n => by positivity
  -- measurability of the fibre function
  have hcont : ContinuousOn (fun v : Euc d => F (Y + v) Y) {v : Euc d | v ≠ 0} := by
    have h1 := hF.1.continuousOn
    refine h1.comp (f := fun v : Euc d => (Y + v, Y)) ((continuous_const.add continuous_id).prodMk
      continuous_const).continuousOn (fun v hv => ?_)
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro h; apply hv; simpa using h
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  have hFm : AEStronglyMeasurable (fun v : Euc d => F (Y + v) Y) volume := by
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure (Euc d)))
      (isOpen_ne.measurableSet : MeasurableSet {v : Euc d | v ≠ 0})
    have e1 : (volume : Measure (Euc d)).restrict {v : Euc d | v ≠ 0} = volume := by
      have := restrict_compl_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
      simpa [Set.compl_singleton_eq] using this
    rwa [e1] at h
  have hKm : AEStronglyMeasurable (fun v : Euc d => ‖z - v‖ ^ e) volume :=
    ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const e).aestronglyMeasurable
  have hFnm : ∀ n, AEStronglyMeasurable (Fn n) volume := fun n => by
    refine hKm.mul (AEStronglyMeasurable.mul ?_ hFm)
    exact ((r26t8a_annulus_contDiff hchi (hR n)).continuous).aestronglyMeasurable
  have hKnn : ∀ v : Euc d, 0 ≤ ‖z - v‖ ^ e := fun v => Real.rpow_nonneg (norm_nonneg _) _
  have hGnn : ∀ v, 0 ≤ G v := fun v => by
    rw [hG]; exact mul_nonneg (hKnn v) (Set.indicator_nonneg (fun w _ => norm_nonneg _) v)
  -- pointwise bound: ‖Fn n v‖ = K |a_n| ‖F‖ ≤ K |a_n| ind ‖F‖
  have hFnb : ∀ n v, ‖Fn n v‖ ≤ |r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v| * G v := fun n v => by
    rw [hFn, hG]; simp only
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hKnn v)]
    by_cases ha : r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v = 0
    · rw [ha]; simp
    · have hv2 : v ∈ closedBall (0 : Euc d) 2 := by
        have := (r26t8a_pu_support hchi n v ha).2
        have h1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        simp only [mem_closedBall, dist_zero_right]; linarith
      rw [Set.indicator_of_mem hv2, Real.norm_eq_abs]
      nlinarith [abs_nonneg (r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v), abs_nonneg (F (Y + v) Y), hKnn v]
  have hFnint : ∀ n, Integrable (Fn n) := fun n => by
    refine (hGi.mono' (hFnm n) (Filter.Eventually.of_forall fun v => ?_))
    refine (hFnb n v).trans ?_
    have := r26t8a_pu_abs_le hchi n v
    nlinarith [hGnn v]
  -- summability of the integrals of the norms
  have hsumm : Summable fun n => ∫ v, ‖Fn n v‖ := by
    refine summable_of_sum_range_le (c := ∫ v, 2 * G v) (fun n => integral_nonneg fun v => norm_nonneg _) ?_
    intro N
    have h1 : ∑ n ∈ Finset.range N, ∫ v, ‖Fn n v‖ = ∫ v, ∑ n ∈ Finset.range N, ‖Fn n v‖ := by
      rw [integral_finset_sum]
      intro n _
      exact (hFnint n).norm
    rw [h1]
    refine integral_mono (integrable_finset_sum _ fun n _ => (hFnint n).norm) (hGi.const_mul 2) (fun v => ?_)
    calc ∑ n ∈ Finset.range N, ‖Fn n v‖ ≤ ∑ n ∈ Finset.range N,
          |r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v| * G v := Finset.sum_le_sum fun n _ => hFnb n v
      _ = (∑ n ∈ Finset.range N, |r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v|) * G v := by rw [Finset.sum_mul]
      _ ≤ 2 * G v := mul_le_mul_of_nonneg_right (r26t8a_pu_sum_le hchi v N) (hGnn v)
  have hsum := hasSum_integral_of_summable_integral_norm hFnint hsumm
  -- identify the sum and the terms
  have hlim : (∫ v, ∑' n, Fn n v) = ∫ v : Euc d, ‖z - v‖ ^ e * (chi v * F (Y + v) Y) := by
    have hae : ∀ᵐ v : Euc d, v ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    have h := ((r26t8a_pu_hasSum hchi v hv).mul_left (‖z - v‖ ^ e * F (Y + v) Y)).tsum_eq
    calc ∑' n, Fn n v = ∑' n : ℕ, (‖z - v‖ ^ e * F (Y + v) Y) *
          r26t8a_annulus chi ((1 / 2 : ℝ) ^ n) v := tsum_congr fun n => by rw [hFn]; simp only; ring
      _ = (‖z - v‖ ^ e * F (Y + v) Y) * chi v := h
      _ = ‖z - v‖ ^ e * (chi v * F (Y + v) Y) := by ring
  rw [hlim] at hsum
  convert hsum using 1
  funext n
  rw [r26t8a_pu_locV_eq hchi alpha (hR n) F X z]

end HRS.MS.R26T8A
