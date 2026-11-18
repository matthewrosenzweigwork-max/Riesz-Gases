import HRS.Uniform.MaximalAux
import HRS.Prob.HilbertBDG

/-!
# Lemma 3.17, first alternative ("two levels"): clause (1) (packet Q01b)

Pathwise integration by parts `∫₀ᵗ V(t,r) dM_r = j M_t + ∫₀ᵗ V(t,r) A_r M_r dr`
(the Riemann sums of the stochastic convolution converge pathwise, uniformly in the partition, to the
right-hand side for every continuous path `M` with `M_0 = 0`), continuity of the right-hand side in `t`,
and the dimension-free Hilbert BDG inequality (`HRS.HilbertBDG.hilbert_bdg`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS
namespace Uniform

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section TwoLevelDet

variable (S : EvolData H E)

/-- `A_r` as a linear map `H → E` when the core is everything. -/
def Aℓ (hD : S.D = ⊤) (r : ℝ) : H →ₗ[ℝ] E :=
  (S.A r) ∘ₗ (LinearMap.codRestrict S.D LinearMap.id (fun x => by rw [hD]; trivial))

theorem Aℓ_apply (hD : S.D = ⊤) (r : ℝ) (x : H) (hx : x ∈ S.D) : Aℓ S hD r x = S.A r ⟨x, hx⟩ := rfl

/-- The integrand `V(t,r) A_r x` of the integrated-by-parts stochastic convolution, cut off to `r ∈ (0,t)`. -/
def Bi (hD : S.D = ⊤) (t r : ℝ) (x : H) : E :=
  (Set.Ioo 0 t).indicator (fun r => S.VE t r (Aℓ S hD r x)) r

variable {S} {T K : ℝ}

theorem Bi_of_mem (hD : S.D = ⊤) {t r : ℝ} (hr : r ∈ Set.Ioo 0 t) (x : H) :
    Bi S hD t r x = S.VE t r (Aℓ S hD r x) := by
  simp [Bi, hr]

theorem Bi_of_not_mem (hD : S.D = ⊤) {t r : ℝ} (hr : r ∉ Set.Ioo 0 t) (x : H) :
    Bi S hD t r x = 0 := by
  simp [Bi, hr]

theorem Bi_sub (hD : S.D = ⊤) (t r : ℝ) (x x' : H) :
    Bi S hD t r (x - x') = Bi S hD t r x - Bi S hD t r x' := by
  by_cases hr : r ∈ Set.Ioo 0 t
  · simp [Bi_of_mem hD hr, map_sub]
  · simp [Bi_of_not_mem hD hr]

theorem EvolData.TwoLevel.K_nonneg (h : S.TwoLevel T K) : 0 ≤ K := (norm_nonneg _).trans h.2.1

theorem EvolData.TwoLevel.norm_Aℓ_le (h : S.TwoLevel T K) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (x : H) :
    ‖Aℓ S h.1 r x‖ ≤ K * ‖x‖ := by
  have hx : x ∈ S.D := by rw [h.1]; trivial
  rw [Aℓ_apply S h.1 r x hx]
  exact h.2.2.2 r hr ⟨x, hx⟩

theorem EvolData.TwoLevel.norm_Bi_le (h : S.TwoLevel T K) {t : ℝ} (ht : t ≤ T) (r : ℝ) (x : H) :
    ‖Bi S h.1 t r x‖ ≤ K * (K * ‖x‖) := by
  have hK := h.K_nonneg
  by_cases hr : r ∈ Set.Ioo 0 t
  · rw [Bi_of_mem h.1 hr]
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le.trans ht⟩
    calc ‖S.VE t r (Aℓ S h.1 r x)‖ ≤ ‖S.VE t r‖ * ‖Aℓ S h.1 r x‖ := (S.VE t r).le_opNorm _
      _ ≤ K * (K * ‖x‖) :=
        mul_le_mul ((h.2.2.1 r t hr.1.le hr.2.le ht).2) (h.norm_Aℓ_le hrT x) (norm_nonneg _) hK
  · rw [Bi_of_not_mem h.1 hr]
    simpa using mul_nonneg hK (mul_nonneg hK (norm_nonneg x))

theorem EvolData.TwoLevel.continuous_Bi (h : S.TwoLevel T K) {t : ℝ} (ht : t ≤ T) (r : ℝ) :
    Continuous (fun x : H => Bi S h.1 t r x) := by
  by_cases hr : r ∈ Set.Ioo 0 t
  · have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le.trans ht⟩
    have : (fun x : H => Bi S h.1 t r x) = fun x => S.VE t r (Aℓ S h.1 r x) := by
      funext x; exact Bi_of_mem h.1 hr x
    rw [this]
    refine (S.VE t r).continuous.comp ?_
    exact (LinearMap.mkContinuous (Aℓ S h.1 r) K (fun x => h.norm_Aℓ_le hrT x)).continuous
  · simp [Bi_of_not_mem h.1 hr]
    exact continuous_const

section Meas

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]

theorem EvolData.TwoLevel.hasDerivAt_V (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (x : H) {r : ℝ} (hr : r ∈ Set.Ioo 0 t) :
    HasDerivAt (fun r' => S.VE t r' (S.j x)) (-(Bi S h.1 t r x)) r := by
  have hx : x ∈ S.D := by rw [h.1]; trivial
  have := hev.deriv t ht ⟨x, hx⟩ r ⟨hr.1.le, hr.2.le⟩
  rw [Bi_of_mem h.1 hr, Aℓ_apply S h.1 r x hx]
  exact this.hasDerivAt (Icc_mem_nhds hr.1 hr.2)

theorem EvolData.TwoLevel.measurable_Bi (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (x : H) : Measurable (fun r => Bi S h.1 t r x) := by
  have : (fun r => Bi S h.1 t r x) =
      (Set.Ioo 0 t).indicator (fun r => -(deriv (fun r' => S.VE t r' (S.j x)) r)) := by
    funext r
    by_cases hr : r ∈ Set.Ioo 0 t
    · rw [Set.indicator_of_mem hr, (h.hasDerivAt_V hev ht x hr).deriv, neg_neg]
    · rw [Set.indicator_of_notMem hr, Bi_of_not_mem h.1 hr]
  rw [this]
  exact ((measurable_deriv _).neg).indicator measurableSet_Ioo

theorem EvolData.TwoLevel.measurable_Bi_path (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {y : ℝ → H} (hy : Continuous y) :
    Measurable (fun r => Bi S h.1 t r (y r)) := by
  have hu : Measurable (Function.uncurry fun (s : ℝ) (r : ℝ) => Bi S h.1 t r (y s)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun r => (h.continuous_Bi ht.2 r).comp hy)
      (fun s => h.measurable_Bi hev ht (y s))
  exact hu.comp (measurable_id.prodMk measurable_id)

theorem EvolData.TwoLevel.norm_Bi_path_le (h : S.TwoLevel T K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {y : ℝ → H} {Y : ℝ} (hY : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖y s‖ ≤ Y) (r : ℝ) :
    ‖Bi S h.1 t r (y r)‖ ≤ (Set.Icc (0 : ℝ) T).indicator (fun _ => K * (K * Y)) r := by
  have hK := h.K_nonneg
  by_cases hr : r ∈ Set.Ioo 0 t
  · have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le.trans ht.2⟩
    rw [Set.indicator_of_mem hrT]
    exact (h.norm_Bi_le ht.2 r (y r)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hY r hrT) hK) hK)
  · rw [Bi_of_not_mem h.1 hr]
    simp only [norm_zero]
    by_cases hrT : r ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hrT]
      exact mul_nonneg hK (mul_nonneg hK ((norm_nonneg _).trans (hY r hrT)))
    · rw [Set.indicator_of_notMem hrT]


theorem EvolData.TwoLevel.integrable_Bi_path (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {y : ℝ → H} (hy : Continuous y) {Y : ℝ}
    (hY : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖y s‖ ≤ Y) :
    Integrable (fun r => Bi S h.1 t r (y r)) := by
  refine Integrable.mono' (g := (Set.Icc (0 : ℝ) T).indicator fun _ => K * (K * Y)) ?_
    (h.measurable_Bi_path hev ht hy).aestronglyMeasurable
    (Eventually.of_forall (h.norm_Bi_path_le ht hY))
  exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))

theorem EvolData.TwoLevel.integrable_Bi_const (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) (x : H) : Integrable (fun r => Bi S h.1 t r x) :=
  h.integrable_Bi_path hev ht (y := fun _ => x) continuous_const (Y := ‖x‖) (fun _ _ => le_rfl)

theorem EvolData.TwoLevel.integral_Bi (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ t) (x : H) :
    ∫ r in a..b, Bi S h.1 t r x = S.VE t a (S.j x) - S.VE t b (S.j x) := by
  have hx : x ∈ S.D := by rw [h.1]; trivial
  have hint : IntervalIntegrable (fun r => -(Bi S h.1 t r x)) volume a b :=
    (h.integrable_Bi_const hev ht x).neg.intervalIntegrable
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun r => S.VE t r (S.j x))
    (f' := fun r => -(Bi S h.1 t r x)) hab ?_ ?_ hint
  · rw [intervalIntegral.integral_neg] at key
    rw [← neg_sub, ← key, neg_neg]
  · intro r hr
    exact (hev.deriv t ht ⟨x, hx⟩ r ⟨ha.trans hr.1, hr.2.trans hb⟩).continuousWithinAt.mono
      (Set.Icc_subset_Icc ha hb)
  · intro r hr
    exact h.hasDerivAt_V hev ht x ⟨ha.trans_lt hr.1, hr.2.trans_le hb⟩

/-- The pathwise limit of the Riemann sums: `j y_t + ∫₀ᵗ V(t,r) A_r y_r dr`. -/
def Zdet (hD : S.D = ⊤) (t : ℝ) (y : ℝ → H) : E := S.j (y t) + ∫ r, Bi S hD t r (y r)

theorem EvolData.TwoLevel.zdet_sub_sum (hev : S.IsEvolution T) (h : S.TwoLevel T K) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {y : ℝ → H} (hy : Continuous y) (hy0 : y 0 = 0)
    {n : ℕ} {ρ : ℕ → ℝ} (hρ0 : ρ 0 = 0) (hρn : ρ n = t) (hρ : ∀ k ≤ n, ρ k ∈ Set.Icc 0 t)
    (hρm : ∀ k < n, ρ k ≤ ρ (k + 1)) {η : ℝ}
    (hη : ∀ k < n, ∀ s ∈ Set.Ioc (ρ k) (ρ (k + 1)), ‖y s - y (ρ (k + 1))‖ ≤ η) :
    ‖Zdet h.1 t y - ∑ k ∈ Finset.range n, S.VE t (ρ k) (S.j (y (ρ (k + 1)) - y (ρ k)))‖ ≤
      K * (K * η) * t := by
  obtain ⟨Y, hY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hy.continuousOn
  have hpath := h.integrable_Bi_path hev ht hy hY
  have hsplit : ∫ r, Bi S h.1 t r (y r) =
      ∑ k ∈ Finset.range n, ∫ r in ρ k..ρ (k + 1), Bi S h.1 t r (y r) := by
    have h1 : ∫ r in Set.Ioc 0 t, Bi S h.1 t r (y r) = ∫ r, Bi S h.1 t r (y r) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr =>
        Bi_of_not_mem h.1 (fun hr' => hr ⟨hr'.1, hr'.2.le⟩) _
    rw [← h1, ← intervalIntegral.integral_of_le ht.1]
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun r => Bi S h.1 t r (y r)) (a := ρ) (n := n) (fun k hk => hpath.intervalIntegrable)
    rw [hρ0, hρn] at this
    exact this.symm
  have hterm : ∀ k < n, S.VE t (ρ k) (S.j (y (ρ (k + 1)) - y (ρ k))) =
      (S.VE t (ρ (k + 1)) (S.j (y (ρ (k + 1)))) - S.VE t (ρ k) (S.j (y (ρ k)))) +
        ∫ r in ρ k..ρ (k + 1), Bi S h.1 t r (y (ρ (k + 1))) := by
    intro k hk
    rw [h.integral_Bi hev ht (hρ k hk.le).1 (hρm k hk) (hρ (k + 1) hk).2]
    simp only [map_sub]
    abel
  have hsum : ∑ k ∈ Finset.range n, S.VE t (ρ k) (S.j (y (ρ (k + 1)) - y (ρ k))) =
      S.j (y t) + ∑ k ∈ Finset.range n, ∫ r in ρ k..ρ (k + 1), Bi S h.1 t r (y (ρ (k + 1))) := by
    rw [Finset.sum_congr rfl fun k hk => hterm k (Finset.mem_range.1 hk), Finset.sum_add_distrib,
      Finset.sum_range_sub (fun k => S.VE t (ρ k) (S.j (y (ρ k))))]
    rw [hρn, hρ0, hy0, hev.self_E t ht]
    simp
  have hdiff : Zdet h.1 t y - ∑ k ∈ Finset.range n, S.VE t (ρ k) (S.j (y (ρ (k + 1)) - y (ρ k))) =
      ∑ k ∈ Finset.range n, ∫ r in ρ k..ρ (k + 1),
        (Bi S h.1 t r (y r) - Bi S h.1 t r (y (ρ (k + 1)))) := by
    rw [hsum, Zdet, hsplit, Finset.sum_congr rfl (fun k hk => intervalIntegral.integral_sub
      (hpath.intervalIntegrable) ((h.integrable_Bi_const hev ht _).intervalIntegrable)),
      Finset.sum_sub_distrib]
    abel
  rw [hdiff]
  calc ‖∑ k ∈ Finset.range n, ∫ r in ρ k..ρ (k + 1),
        (Bi S h.1 t r (y r) - Bi S h.1 t r (y (ρ (k + 1))))‖
      ≤ ∑ k ∈ Finset.range n, K * (K * η) * (ρ (k + 1) - ρ k) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hk := Finset.mem_range.1 hk
        have := intervalIntegral.norm_integral_le_of_norm_le_const (a := ρ k) (b := ρ (k + 1))
          (C := K * (K * η)) (f := fun r => Bi S h.1 t r (y r) - Bi S h.1 t r (y (ρ (k + 1))))
          (fun r hr => by
            rw [Set.uIoc_of_le (hρm k hk)] at hr
            rw [← Bi_sub]
            exact (h.norm_Bi_le ht.2 r _).trans
              (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hη k hk r hr) h.K_nonneg)
                h.K_nonneg))
        rwa [abs_of_nonneg (sub_nonneg.2 (hρm k hk))] at this
    _ = K * (K * η) * t := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k => ρ k), hρn, hρ0, sub_zero]

theorem EvolData.TwoLevel.continuousOn_zdet (hev : S.IsEvolution T) (h : S.TwoLevel T K) {y : ℝ → H}
    (hy : Continuous y) : ContinuousOn (fun t => Zdet h.1 t y) (Set.Icc 0 T) := by
  intro t0 ht0
  obtain ⟨Y, hY⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hy.continuousOn
  have h1 : ContinuousWithinAt (fun t => S.j (y t)) (Set.Icc 0 T) t0 :=
    (S.j.continuous.comp hy).continuousWithinAt
  have h2 : ContinuousWithinAt (fun t => ∫ r, Bi S h.1 t r (y r)) (Set.Icc 0 T) t0 := by
    refine continuousWithinAt_of_dominated
      (bound := (Set.Icc (0 : ℝ) T).indicator fun _ => K * (K * Y)) ?_ ?_ ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun t ht =>
        (h.measurable_Bi_path hev ht hy).aestronglyMeasurable
    · exact eventually_nhdsWithin_of_forall fun t ht =>
        Eventually.of_forall (h.norm_Bi_path_le ht hY)
    · exact (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
    · have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ ({t0} : Set ℝ) :=
        (Set.countable_singleton t0).ae_notMem volume
      filter_upwards [hne] with r hr
      have hr : r ≠ t0 := by simpa using hr
      rcases lt_or_gt_of_ne hr with hlt | hgt
      · by_cases hr0 : r ≤ 0
        · have : (fun t => Bi S h.1 t r (y r)) = fun _ => 0 :=
            funext fun t => Bi_of_not_mem h.1 (fun hh => absurd hh.1 (not_lt.2 hr0)) _
          rw [this]; exact continuousWithinAt_const
        · push Not at hr0
          have hc : ContinuousWithinAt (fun t => S.VE t r (Aℓ S h.1 r (y r))) (Set.Icc r T) t0 := by
            have := hev.cont_E (Aℓ S h.1 r (y r)) (t0, r) ⟨hr0.le, hlt.le, ht0.2⟩
            have hf : ContinuousWithinAt (fun t : ℝ => (t, r)) (Set.Icc r T) t0 :=
              continuousWithinAt_id.prodMk continuousWithinAt_const
            exact ContinuousWithinAt.comp (f := fun t : ℝ => (t, r)) this hf
              (fun t ht => ⟨hr0.le, ht.1, ht.2⟩)
          have hc' : ContinuousWithinAt (fun t => S.VE t r (Aℓ S h.1 r (y r))) (Set.Icc 0 T) t0 :=
            hc.mono_of_mem_nhdsWithin
              (mem_nhdsWithin.2 ⟨Set.Ioi r, isOpen_Ioi, hlt, fun t ht => ⟨ht.1.le, ht.2.2⟩⟩)
          refine hc'.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hlt)] with t ht
            exact Bi_of_mem h.1 ⟨hr0, ht⟩ _
          · exact Bi_of_mem h.1 ⟨hr0, hlt⟩ _
      · have : (fun t => Bi S h.1 t r (y r)) =ᶠ[𝓝[Set.Icc 0 T] t0] fun _ => 0 := by
          filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hgt)] with t ht
          exact Bi_of_not_mem h.1 (fun hh => absurd hh.2 (not_lt.2 ht.le)) _
        exact continuousWithinAt_const.congr_of_eventuallyEq this
          (Bi_of_not_mem h.1 (fun hh => absurd hh.2 (not_lt.2 hgt.le)) _)
  exact h1.add h2

theorem EvolData.TwoLevel.norm_zdet_le (h : S.TwoLevel T K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {y : ℝ → H} {Y : ℝ} (hY : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖y s‖ ≤ Y) (hy : Continuous y)
    (hev : S.IsEvolution T) :
    ‖Zdet h.1 t y‖ ≤ (K + K * (K * T)) * Y := by
  have hK := h.K_nonneg
  have hY0 : 0 ≤ Y := (norm_nonneg _).trans (hY 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  have h1 : ‖S.j (y t)‖ ≤ K * Y :=
    (S.j.le_opNorm _).trans (mul_le_mul h.2.1 (hY t ht) (norm_nonneg _) hK)
  have h2 : ‖∫ r, Bi S h.1 t r (y r)‖ ≤ K * (K * T) * Y := by
    have := norm_integral_le_of_norm_le (μ := volume)
      (g := (Set.Icc (0 : ℝ) T).indicator fun _ => K * (K * Y))
      ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp)))
      (Eventually.of_forall (h.norm_Bi_path_le ht hY))
    refine this.trans ?_
    rw [integral_indicator measurableSet_Icc]
    simp [Measure.real, Real.volume_Icc, ht.1.trans ht.2]
    nlinarith [mul_nonneg hK hK, mul_nonneg (mul_nonneg hK hK) hY0]
  calc ‖Zdet h.1 t y‖ ≤ ‖S.j (y t)‖ + ‖∫ r, Bi S h.1 t r (y r)‖ := norm_add_le _ _
    _ ≤ K * Y + K * (K * T) * Y := add_le_add h1 h2
    _ = (K + K * (K * T)) * Y := by ring

end Meas

end TwoLevelDet

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {S : EvolData H E} {T K : ℝ}

/-- The (clamped) sample path of `M`. -/
def pathOf (T : ℝ) (M : ℝ → Ω → H) (ω : Ω) : ℝ → H := fun s => M (HilbertBDG.clampT T s) ω

/-- The stochastic convolution, defined pathwise by integration by parts. -/
def Zc (hD : S.D = ⊤) (T : ℝ) (M : ℝ → Ω → H) (t : ℝ) (ω : Ω) : E := Zdet hD t (pathOf T M ω)

/-- The supremum norm of a path (in `ℝ≥0∞`). -/
def supNorm (T : ℝ) (M : ℝ → Ω → H) (ω : Ω) : ℝ≥0∞ := ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ

theorem pathOf_of_mem {M : ℝ → Ω → H} {ω : Ω} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    pathOf T M ω s = M s ω := by
  simp [pathOf, HilbertBDG.clampT_of_mem hs]

theorem continuous_pathOf (hT : 0 ≤ T) {M : ℝ → Ω → H} {ω : Ω}
    (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) : Continuous (pathOf T M ω) :=
  hc.comp_continuous (HilbertBDG.continuous_clampT T) (HilbertBDG.clampT_mem hT)

theorem pathOf_zero (hT : 0 ≤ T) {M : ℝ → Ω → H} {ω : Ω} (h0 : M 0 ω = 0) :
    pathOf T M ω 0 = 0 := by
  rw [pathOf_of_mem ⟨le_rfl, hT⟩, h0]

theorem exists_bound_path (hT : 0 ≤ T) {M : ℝ → Ω → H} {ω : Ω}
    (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) :
    ∃ Y : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖M s ω‖ ≤ Y := by
  obtain ⟨Y, hY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hc
  exact ⟨Y, hY⟩

theorem supNorm_lt_top (hT : 0 ≤ T) {M : ℝ → Ω → H} {ω : Ω}
    (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) : supNorm T M ω < ∞ := by
  obtain ⟨Y, hY⟩ := exists_bound_path hT hc
  refine lt_of_le_of_lt (iSup₂_le fun s hs => ?_) (ENNReal.ofReal_lt_top (r := Y))
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hY s hs)

theorem norm_le_supNorm_toReal (hT : 0 ≤ T) {M : ℝ → Ω → H} {ω : Ω}
    (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ‖M s ω‖ ≤ (supNorm T M ω).toReal := by
  have h1 : ‖M s ω‖ₑ ≤ supNorm T M ω := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => ‖M t ω‖ₑ) s hs
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_iff_le_toReal (supNorm_lt_top hT hc).ne).1 h1

/-- Riemann sums as sums over `ℕ`-indexed partitions, and the pathwise estimate. -/
theorem EvolData.TwoLevel.rs_est (hT : 0 ≤ T) (hev : S.IsEvolution T) (h : S.TwoLevel T K) {M : ℝ → Ω → H}
    {ω : Ω} (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) (h0 : M 0 ω = 0) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ} (r : Fin (n + 1) → ℝ) (hr0 : r 0 = 0)
    (hrl : r (Fin.last n) = t) (hmono : Monotone r) {η : ℝ}
    (hη : ∀ i : Fin n, ∀ s ∈ Set.Ioc (r i.castSucc) (r i.succ),
      ‖pathOf T M ω s - pathOf T M ω (r i.succ)‖ ≤ η) :
    ‖Zc h.1 T M t ω - riemannSum S.VE S.j M t r ω‖ ≤ K * (K * η) * t := by
  have hrmem : ∀ i, r i ∈ Set.Icc (0 : ℝ) t := fun i =>
    ⟨hr0 ▸ hmono (Fin.zero_le i), hrl ▸ hmono (Fin.le_last i)⟩
  have hrT : ∀ i, r i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨(hrmem i).1, (hrmem i).2.trans ht.2⟩
  set ρ : ℕ → ℝ := fun k => r ⟨min k n, Nat.lt_succ_of_le (min_le_right _ _)⟩ with hρ
  have hρc : ∀ k (hk : k < n), ρ k = r (Fin.castSucc ⟨k, hk⟩) := by
    intro k hk; simp only [hρ]; congr 1; ext; simp [Nat.min_eq_left hk.le]
  have hρs : ∀ k (hk : k < n), ρ (k + 1) = r (Fin.succ ⟨k, hk⟩) := by
    intro k hk; simp only [hρ]; congr 1; ext; simp [Nat.min_eq_left (Nat.succ_le_of_lt hk)]
  have hρ0 : ρ 0 = 0 := by
    simp only [hρ]; rw [← hr0]; congr 1
  have hρn : ρ n = t := by
    simp only [hρ]; rw [← hrl]; congr 1; ext; simp
  have hrs : riemannSum S.VE S.j M t r ω =
      ∑ k ∈ Finset.range n, S.VE t (ρ k)
        (S.j (pathOf T M ω (ρ (k + 1)) - pathOf T M ω (ρ k))) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => S.VE t (ρ k)
        (S.j (pathOf T M ω (ρ (k + 1)) - pathOf T M ω (ρ k)))) n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := hρc i i.2
    have e2 := hρs i i.2
    simp only [Fin.eta] at e1 e2
    rw [e1, e2, pathOf_of_mem (hrT _), pathOf_of_mem (hrT _)]
  rw [hrs]
  refine h.zdet_sub_sum hev ht (continuous_pathOf hT hc) (pathOf_zero hT h0) hρ0 hρn ?_ ?_ ?_
  · intro k hk
    by_cases hkn : k < n
    · rw [hρc k hkn]; exact hrmem _
    · have : k = n := le_antisymm hk (not_lt.1 hkn)
      rw [this, hρn]; exact ⟨ht.1, le_rfl⟩
  · intro k hk
    rw [hρc k hk, hρs k hk]
    exact hmono (Fin.castSucc_le_succ _)
  · intro k hk s hs
    rw [hρc k hk, hρs k hk] at hs
    rw [hρs k hk]
    exact hη ⟨k, hk⟩ s hs

/-- A pathwise bound for `Zc` minus any Riemann sum, in terms of the sup norm. -/
theorem EvolData.TwoLevel.enorm_Zc_sub_rs_le (hT : 0 ≤ T) (hev : S.IsEvolution T) (h : S.TwoLevel T K)
    {M : ℝ → Ω → H} {ω : Ω} (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) (h0 : M 0 ω = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ} (r : Fin (n + 1) → ℝ) (hr0 : r 0 = 0)
    (hrl : r (Fin.last n) = t) (hmono : Monotone r) :
    ‖Zc h.1 T M t ω - riemannSum S.VE S.j M t r ω‖ₑ ≤
      ENNReal.ofReal (2 * (K * (K * T))) * supNorm T M ω := by
  have hK := h.K_nonneg
  set Y := (supNorm T M ω).toReal with hYdef
  have hY : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖M s ω‖ ≤ Y := fun s hs => norm_le_supNorm_toReal hT hc hs
  have hY0 : 0 ≤ Y := ENNReal.toReal_nonneg
  have hrmem : ∀ i, r i ∈ Set.Icc (0 : ℝ) t := fun i =>
    ⟨hr0 ▸ hmono (Fin.zero_le i), hrl ▸ hmono (Fin.le_last i)⟩
  have hrT : ∀ i, r i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨(hrmem i).1, (hrmem i).2.trans ht.2⟩
  have := h.rs_est hT hev hc h0 ht r hr0 hrl hmono (η := 2 * Y) (fun i s hs => by
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨(hrT i.castSucc).1.trans hs.1.le, hs.2.trans (hrT i.succ).2⟩
    rw [pathOf_of_mem hsT, pathOf_of_mem (hrT _)]
    calc ‖M s ω - M (r i.succ) ω‖ ≤ ‖M s ω‖ + ‖M (r i.succ) ω‖ := norm_sub_le _ _
      _ ≤ 2 * Y := by linarith [hY s hsT, hY _ (hrT i.succ)])
  rw [← ofReal_norm]
  have hfin : supNorm T M ω = ENNReal.ofReal Y :=
    (ENNReal.ofReal_toReal (supNorm_lt_top hT hc).ne).symm
  rw [hfin, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (this.trans ?_)
  have hKK := mul_nonneg hK hK
  nlinarith [mul_nonneg hKK hY0, mul_nonneg (mul_nonneg hKK hY0) (sub_nonneg.2 ht.2)]

theorem EvolData.TwoLevel.rs_tendsto (hT : 0 ≤ T) (hev : S.IsEvolution T) (h : S.TwoLevel T K)
    {M : ℝ → Ω → H} {ω : Ω} (hc : ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) (h0 : M 0 ω = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {n : ℕ → ℕ} (r : ∀ m, Fin (n m + 1) → ℝ)
    (hr0 : ∀ m, r m 0 = 0) (hrl : ∀ m, r m (Fin.last (n m)) = t) (hmono : ∀ m, Monotone (r m))
    (hmesh : ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ i : Fin (n m), r m i.succ - r m i.castSucc < δ) :
    Tendsto (fun m => riemannSum S.VE S.j M t (r m) ω) atTop (𝓝 (Zc h.1 T M t ω)) := by
  have hK := h.K_nonneg
  have hpc := continuous_pathOf hT hc
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hpc.continuousOn
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / (2 * (K * K * T + 1)) with hη
  have hKT : 0 ≤ K * K * T := mul_nonneg (mul_nonneg hK hK) hT
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc η hηpos
  obtain ⟨N, hN⟩ := hmesh δ hδ
  refine ⟨N, fun m hm => ?_⟩
  have hrmem : ∀ i, r m i ∈ Set.Icc (0 : ℝ) t := fun i =>
    ⟨hr0 m ▸ hmono m (Fin.zero_le i), hrl m ▸ hmono m (Fin.le_last i)⟩
  have hrT : ∀ i, r m i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨(hrmem i).1, (hrmem i).2.trans ht.2⟩
  have key := h.rs_est hT hev hc h0 ht (r m) (hr0 m) (hrl m) (hmono m) (η := η) (fun i s hs => by
    have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨(hrT i.castSucc).1.trans hs.1.le, hs.2.trans (hrT i.succ).2⟩
    have := hδ' s hsT _ (hrT i.succ) (by
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.2])]
      linarith [hN m hm i, hs.1])
    rw [dist_eq_norm] at this
    exact this.le)
  rw [dist_comm, dist_eq_norm]
  refine lt_of_le_of_lt key ?_
  have h1 : K * (K * η) * t ≤ K * K * T * η := by
    have : K * (K * η) * t = (K * K) * η * t := by ring
    rw [this]
    have := mul_nonneg (mul_nonneg hK hK) hηpos.le
    nlinarith [mul_le_mul_of_nonneg_left ht.2 this]
  refine lt_of_le_of_lt h1 ?_
  have h2 : K * K * T * η = ε * (K * K * T) / (2 * (K * K * T + 1)) := by
    rw [hη]; ring
  rw [h2, div_lt_iff₀ (by positivity)]
  nlinarith

/-- Uniform partitions of `[0,t]` into `m+1` pieces. -/
def unifPart (t : ℝ) (m : ℕ) : Fin (m + 1 + 1) → ℝ := fun i => t * (i : ℝ) / ((m : ℝ) + 1)

theorem unifPart_zero (t : ℝ) (m : ℕ) : unifPart t m 0 = 0 := by simp [unifPart]

theorem unifPart_last (t : ℝ) (m : ℕ) : unifPart t m (Fin.last (m + 1)) = t := by
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp [unifPart]
  field_simp

theorem unifPart_mono {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : Monotone (unifPart t m) := by
  intro i j hij
  have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  unfold unifPart
  gcongr

theorem unifPart_mesh (t : ℝ) (m : ℕ) (i : Fin (m + 1)) :
    unifPart t m i.succ - unifPart t m i.castSucc = t / ((m : ℝ) + 1) := by
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  simp [unifPart]
  field_simp
  ring

theorem aemeasurable_rs {M : ℝ → Ω → H} (hMeas : ∀ s ∈ Set.Icc (0 : ℝ) T, AEMeasurable (M s) P)
    {t : ℝ} {n : ℕ} (r : Fin (n + 1) → ℝ) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) T) :
    AEMeasurable (riemannSum S.VE S.j M t r) P := by
  unfold riemannSum
  refine Finset.aemeasurable_fun_sum _ fun i _ => ?_
  exact ((S.VE t (r i.castSucc)).continuous.comp S.j.continuous).measurable.comp_aemeasurable
    ((hMeas _ (hr _)).sub (hMeas _ (hr _)))

theorem EvolData.TwoLevel.aemeasurable_Zc (hT : 0 ≤ T) (hev : S.IsEvolution T) (h : S.TwoLevel T K)
    {M : ℝ → Ω → H} (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T))
    (hzero : ∀ᵐ ω ∂P, M 0 ω = 0) (hMeas : ∀ s ∈ Set.Icc (0 : ℝ) T, AEMeasurable (M s) P)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) : AEMeasurable (Zc h.1 T M t) P := by
  have hrT : ∀ m i, unifPart t m i ∈ Set.Icc (0 : ℝ) T := fun m i =>
    ⟨(unifPart_zero t m ▸ unifPart_mono ht.1 m (Fin.zero_le i)),
      (unifPart_last t m ▸ unifPart_mono ht.1 m (Fin.le_last i)).trans ht.2⟩
  refine aemeasurable_of_tendsto_metrizable_ae atTop
    (f := fun m => riemannSum S.VE S.j M t (unifPart t m))
    (fun m => aemeasurable_rs hMeas _ (hrT m)) ?_
  filter_upwards [hcont, hzero] with ω hc h0
  refine h.rs_tendsto hT hev hc h0 ht (n := fun m => m + 1) (unifPart t)
    (fun m => unifPart_zero t m) (fun m => unifPart_last t m) (fun m => unifPart_mono ht.1 m) ?_
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N, fun m hm i => ?_⟩
  rw [unifPart_mesh]
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hN
  nlinarith

theorem EvolData.TwoLevel.isStochConv {P : Measure Ω} [IsProbabilityMeasure P]
    (hT : 0 ≤ T) (hev : S.IsEvolution T) (h : S.TwoLevel T K)
    {M : ℝ → Ω → H} (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T))
    (hzero : ∀ᵐ ω ∂P, M 0 ω = 0) (hMeas : ∀ s ∈ Set.Icc (0 : ℝ) T, AEMeasurable (M s) P)
    (hfin : ∫⁻ ω, (supNorm T M ω) ^ 2 ∂P ≠ ∞) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    IsStochConv P S.VE S.j M 0 t (Zc h.1 T M t) := by
  intro ε hε
  by_contra hcon
  push Not at hcon
  choose n r h0 hl hmono hmesh hge using fun m : ℕ => hcon (1 / ((m : ℝ) + 1)) (by positivity)
  have hrT : ∀ m i, r m i ∈ Set.Icc (0 : ℝ) T := fun m i =>
    ⟨(h0 m ▸ hmono m (Fin.zero_le i)), (hl m ▸ hmono m (Fin.le_last i)).trans ht.2⟩
  have hZ := h.aemeasurable_Zc hT hev hcont hzero hMeas ht
  have hlim : Tendsto (fun m => ∫⁻ ω, ‖Zc h.1 T M t ω - riemannSum S.VE S.j M t (r m) ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 (∫⁻ _ω, (0 : ℝ≥0∞) ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence'
      (fun ω => (ENNReal.ofReal (2 * (K * (K * T))) * supNorm T M ω) ^ 2) ?_ ?_ ?_ ?_
    · intro m
      exact ((hZ.sub (aemeasurable_rs hMeas _ (hrT m))).enorm).pow_const 2
    · intro m
      filter_upwards [hcont, hzero] with ω hc h0'
      exact pow_le_pow_left' (h.enorm_Zc_sub_rs_le hT hev hc h0' ht (r m) (h0 m) (hl m)
        (hmono m)) 2
    · have : ∫⁻ ω, (ENNReal.ofReal (2 * (K * (K * T))) * supNorm T M ω) ^ 2 ∂P =
          ENNReal.ofReal (2 * (K * (K * T))) ^ 2 * ∫⁻ ω, (supNorm T M ω) ^ 2 ∂P := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      rw [this]
      exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hfin
    · filter_upwards [hcont, hzero] with ω hc h0'
      have hmesh' : ∀ δ > 0, ∃ N, ∀ m ≥ N, ∀ i : Fin (n m), r m i.succ - r m i.castSucc < δ := by
        intro δ hδ
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
        refine ⟨N, fun m hm i => lt_of_lt_of_le (hmesh m i) ?_⟩
        have hm' : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm
        exact (one_div_le_one_div_of_le (by positivity) hm').trans hN.le
      have := h.rs_tendsto hT hev hc h0' ht r h0 hl hmono hmesh'
      have h1 : Tendsto (fun m => edist (Zc h.1 T M t ω) (riemannSum S.VE S.j M t (r m) ω))
          atTop (𝓝 0) := by
        simpa [edist_comm] using tendsto_iff_edist_tendsto_0.1 this
      have h2 := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
      simpa [Function.comp_def, edist_eq_enorm_sub] using h2
  have := ge_of_tendsto' hlim fun m => hge m
  simp at this
  linarith

theorem supNorm_sq_ne_top {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology H] {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) :
    ∫⁻ ω, (supNorm T M ω) ^ 2 ∂P ≠ ∞ := by
  obtain ⟨C, -, hC⟩ := HilbertBDG.hilbert_bdg 2 le_rfl
  have h1 := hC Ω P ℱ H T M Sg hM
  have hR : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^
      ((2 : ℝ) / 2) ∂P < ∞ := by
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
    have : ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ∂P =
        ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) T, traceNormForm (Sg r ω)) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hM.sigma_pathint] with ω hω
      exact (ofReal_integral_eq_lintegral_ofReal hω
        (Eventually.of_forall fun _ => traceNormForm_nonneg _)).symm
    rw [this]
    exact hM.sigma_int.lintegral_lt_top
  have h2 : ∫⁻ ω, (supNorm T M ω) ^ (2 : ℝ) ∂P < ∞ :=
    lt_of_le_of_lt h1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hR)
  simp only [ENNReal.rpow_two] at h2
  exact h2.ne

/-- **Lemma 3.17, clause (1) and clause (2), first alternative ("two levels").**  This is exactly
`HRS.Uniform.maximal_estimate` with the hypothesis `S.MaxHyp T K` replaced by its first disjunct. -/
theorem maximal_estimate_twoLevel (T p K : ℝ) (hT : 0 ≤ T) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ)
        (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
        (S : EvolData H E) (hS : S.IsEvolution T ∧ S.TwoLevel T K)
        (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
        (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg),
        ∃ Z : ℝ → Ω → E,
          (∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t)) ∧
          (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) ∧
          (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ω‖ₑ) ^ p ∂P) ^ (1 / p) ≤
            ENNReal.ofReal C *
              (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P) ^ (1 / p)) ∧
      (∀ (H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        (S : EvolData H E) (hS : S.IsEvolution T ∧ S.TwoLevel T K) (b : ℝ → H),
        ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖∫ r in Set.Icc (0 : ℝ) t, S.VE t r (S.j (b r))‖ₑ ≤
          ENNReal.ofReal C * ∫⁻ r in Set.Icc (0 : ℝ) T, ‖b r‖ₑ) := by
  obtain ⟨Cb, hCb0, hCb⟩ := HilbertBDG.hilbert_bdg p hp
  have hp0 : 0 < p := by linarith
  set c : ℝ := |K| + |K| * (|K| * T) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max (detConst T K) (c * Cb ^ (1 / p)), le_max_of_le_left (detConst_pos T K).le, ?_, ?_⟩
  · intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS M Sg hM
    obtain ⟨hev, h⟩ := hS
    have hK := h.K_nonneg
    have hcont := hM.cont
    have hzero := hM.zero
    have hMeas : ∀ s ∈ Set.Icc (0 : ℝ) T, AEMeasurable (M s) P := fun s hs =>
      (hM.sq_int s hs).aestronglyMeasurable.aemeasurable
    have hfin := supNorm_sq_ne_top hM
    refine ⟨Zc h.1 T M, fun t ht => h.isStochConv hT hev hcont hzero hMeas hfin ht, ?_, ?_⟩
    · filter_upwards [hcont] with ω hc'
      exact h.continuousOn_zdet hev (continuous_pathOf hT hc')
    · have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zc h.1 T M t ω‖ₑ) ≤
          ENNReal.ofReal (K + K * (K * T)) * supNorm T M ω := by
        filter_upwards [hcont] with ω hc'
        refine iSup₂_le fun t ht => ?_
        have hY : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖pathOf T M ω s‖ ≤ (supNorm T M ω).toReal := by
          intro s hs
          rw [pathOf_of_mem hs]
          exact norm_le_supNorm_toReal hT hc' hs
        have hn := h.norm_zdet_le ht hY (continuous_pathOf hT hc') hev
        rw [← ofReal_norm]
        have hfin' : supNorm T M ω = ENNReal.ofReal (supNorm T M ω).toReal :=
          (ENNReal.ofReal_toReal (supNorm_lt_top hT hc').ne).symm
        rw [hfin', ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hn
      have hcK : c = K + K * (K * T) := by
        rw [hc, abs_of_nonneg hK]
      set R := ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^
        (p / 2) ∂P with hR
      have hbdg : ∫⁻ ω, (supNorm T M ω) ^ p ∂P ≤ ENNReal.ofReal Cb * R := hCb Ω P ℱ H T M Sg hM
      calc (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zc h.1 T M t ω‖ₑ) ^ p ∂P) ^ (1 / p)
          ≤ (∫⁻ ω, (ENNReal.ofReal (K + K * (K * T)) * supNorm T M ω) ^ p ∂P) ^ (1 / p) := by
            refine ENNReal.rpow_le_rpow (lintegral_mono_ae (hpt.mono fun ω hω => ?_)) (by positivity)
            exact ENNReal.rpow_le_rpow hω hp0.le
        _ = (ENNReal.ofReal (K + K * (K * T)) ^ p * ∫⁻ ω, (supNorm T M ω) ^ p ∂P) ^ (1 / p) := by
            congr 1
            simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
            exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top)
        _ ≤ (ENNReal.ofReal (K + K * (K * T)) ^ p * (ENNReal.ofReal Cb * R)) ^ (1 / p) :=
            ENNReal.rpow_le_rpow (mul_le_mul' le_rfl hbdg) (by positivity)
        _ = ENNReal.ofReal (c * Cb ^ (1 / p)) * R ^ (1 / p) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
              mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
              ENNReal.ofReal_mul hc0, ENNReal.ofReal_rpow_of_nonneg hCb0 (by positivity), hcK]
            ring
        _ ≤ ENNReal.ofReal (max (detConst T K) (c * Cb ^ (1 / p))) * R ^ (1 / p) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  · intro H E _ _ _ _ _ S hS b
    refine (maximal_deterministic T K hT S ⟨hS.1, Or.inl hS.2⟩ b).trans ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl

end Prob

end Uniform
end HRS
