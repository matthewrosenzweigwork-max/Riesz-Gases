import HRS.MC.CepP4Aux2

/-!
# Packet P4, Aux3: test functions vanishing near the collisions and the cube integral of `ψ · f`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

/-- Continuous, nonnegative test functions on `Config d N` vanishing on the `δ`-neighbourhood of the collisions. -/
def Good (ψ : Config d N → ℝ) (δ : ℝ) : Prop :=
  Continuous ψ ∧ (∀ x, 0 ≤ ψ x) ∧ 0 < δ ∧ ∀ x, ψ x ≠ 0 → δ ≤ Metric.infDist x (collisionSet d N)

theorem Good.notMem {ψ : Config d N → ℝ} {δ : ℝ} (h : Good ψ δ) {x : Config d N} (hx : ψ x ≠ 0) :
    x ∉ collisionSet d N := by
  intro hc
  have := h.2.2.2 x hx
  rw [Metric.infDist_zero_of_mem hc] at this
  exact absurd this (not_le.2 h.2.2.1)

theorem mem_liftedFree_of_infDist {δ : ℝ} (hδ : 0 < δ) {Y : Fin N → Euc d}
    (hY : δ ≤ Metric.infDist (mkC Y) (collisionSet d N)) : Y ∈ liftedFree d N := by
  show mkC Y ∉ collisionSet d N
  intro hc
  rw [Metric.infDist_zero_of_mem hc] at hY
  exact absurd hY (not_le.2 hδ)

/-- The compact set carrying the support of `ψ ∘ mkC` on the cube. -/
def Kset (d N : ℕ) (δ : ℝ) : Set (Fin N → Euc d) :=
  closure (cubeQ d N) ∩ {Y | δ ≤ Metric.infDist (mkC Y) (collisionSet d N)}

theorem isBounded_cubeQ : Bornology.IsBounded (cubeQ d N) :=
  (Metric.isBounded_closedBall (x := (0 : Fin N → Euc d)) (r := Real.sqrt d)).subset (fun Y hY => by
    rw [mem_closedBall_zero_iff]
    have := norm_repC_le (mkC Y)
    rwa [repC_mkC_of_mem hY] at this)

theorem isCompact_Kset (δ : ℝ) : IsCompact (Kset d N δ) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ (isBounded_cubeQ.closure.subset inter_subset_left)
  exact isClosed_closure.inter (isClosed_le continuous_const
    ((Metric.continuous_infDist_pt (collisionSet d N)).comp continuous_mkC))

theorem Kset_sub {δ : ℝ} (hδ : 0 < δ) : Kset d N δ ⊆ liftedFree d N :=
  fun _ hY => mem_liftedFree_of_infDist hδ hY.2

theorem vanish_off_Kset {ψ : Config d N → ℝ} {δ : ℝ} (h : Good ψ δ) {Y : Fin N → Euc d}
    (hY : Y ∈ cubeQ d N) (hK : Y ∉ Kset d N δ) : ψ (mkC Y) = 0 := by
  by_contra hne
  exact hK ⟨subset_closure hY, h.2.2.2 _ hne⟩

theorem ghat_of_mem {f : ℝ → Config d N → ℝ} {T : ℝ} {p : ℝ × (Fin N → Euc d)}
    (hp : p ∈ Ioo 0 T ×ˢ liftedFree d N) : ghat f T p = f p.1 (mkC p.2) := by
  unfold ghat; rw [Set.indicator_of_mem hp]

theorem bound_F {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hgc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (Ioo 0 T ×ˢ liftedFree d N))
    {ψ : Config d N → ℝ} {δ : ℝ} (hψ : Good ψ δ) {a b : ℝ} (ha : 0 < a) (hb : b < T) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, ∀ Y ∈ cubeQ d N, ‖ψ (mkC Y) * ghat f T (t, Y)‖ ≤ M := by
  obtain ⟨Mψ, hMψ⟩ := isCompact_univ.exists_bound_of_continuousOn hψ.1.continuousOn
  have hcpt : IsCompact (Icc a b ×ˢ Kset d N δ) := isCompact_Icc.prod (isCompact_Kset δ)
  have hsub : Icc a b ×ˢ Kset d N δ ⊆ Ioo 0 T ×ˢ liftedFree d N := fun p hp =>
    ⟨⟨lt_of_lt_of_le ha hp.1.1, lt_of_le_of_lt hp.1.2 hb⟩, Kset_sub hψ.2.2.1 hp.2⟩
  obtain ⟨Mg, hMg⟩ := hcpt.exists_bound_of_continuousOn (hgc.mono hsub)
  refine ⟨max (Mψ * Mg) 0, fun t ht Y hY => ?_⟩
  by_cases hK : Y ∈ Kset d N δ
  · have hp : (t, Y) ∈ Icc a b ×ˢ Kset d N δ := ⟨ht, hK⟩
    have h1 := hMg (t, Y) hp
    have h2 := hMψ (mkC Y) (mem_univ _)
    rw [ghat_of_mem (hsub hp)]
    refine le_trans ?_ (le_max_left _ _)
    rw [norm_mul]
    exact mul_le_mul h2 h1 (norm_nonneg _) (le_trans (norm_nonneg _) h2)
  · rw [vanish_off_Kset hψ hY hK]; simp

theorem integrableOn_cube {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hgc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (Ioo 0 T ×ˢ liftedFree d N))
    (hfs : Measurable (ghat f T))
    {ψ : Config d N → ℝ} {δ : ℝ} (hψ : Good ψ δ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IntegrableOn (fun Y => ψ (mkC Y) * ghat f T (t, Y)) (cubeQ d N) := by
  obtain ⟨M, hM⟩ := bound_F hgc hψ (a := t) (b := t) ht.1 ht.2
  refine Measure.integrableOn_of_bounded (M := M) isBounded_cubeQ.measure_lt_top.ne ?_ ?_
  · exact (hψ.1.comp continuous_mkC).measurable.aestronglyMeasurable.mul
      (hfs.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_cubeQ).2 (Eventually.of_forall fun Y hY =>
      hM t ⟨le_rfl, le_rfl⟩ Y hY)

/-- The cube integral of `ψ · g(t, ·)`. -/
def Bfun (f : ℝ → Config d N → ℝ) (T : ℝ) (ψ : Config d N → ℝ) (t : ℝ) : ℝ :=
  ∫ Y in cubeQ d N, ψ (mkC Y) * ghat f T (t, Y)

theorem continuousAt_Bfun {f : ℝ → Config d N → ℝ} {T : ℝ}
    (hgc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (Ioo 0 T ×ˢ liftedFree d N))
    (hfs : Measurable (ghat f T))
    {ψ : Config d N → ℝ} {δ : ℝ} (hψ : Good ψ δ) {t0 : ℝ} (ht0 : t0 ∈ Ioo 0 T) :
    ContinuousAt (Bfun f T ψ) t0 := by
  have ha : 0 < t0 / 2 := by linarith [ht0.1]
  have hb : (t0 + T) / 2 < T := by linarith [ht0.2]
  obtain ⟨M, hM⟩ := bound_F hgc hψ ha hb
  have hnhds : Icc (t0 / 2) ((t0 + T) / 2) ∈ 𝓝 t0 :=
    Icc_mem_nhds (by linarith [ht0.1]) (by linarith [ht0.2])
  have hO : IsOpen (Ioo 0 T ×ˢ liftedFree d N : Set (ℝ × (Fin N → Euc d))) :=
    isOpen_Ioo.prod (isOpen_liftedFree d N)
  haveI : IsFiniteMeasure ((volume : Measure (Fin N → Euc d)).restrict (cubeQ d N)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isBounded_cubeQ.measure_lt_top⟩
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun t => ?_
    exact (hψ.1.comp continuous_mkC).measurable.aestronglyMeasurable.mul
      (hfs.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [hnhds] with t ht
    exact (ae_restrict_iff' measurableSet_cubeQ).2 (Eventually.of_forall fun Y hY => hM t ht Y hY)
  · exact integrable_const M
  · refine (ae_restrict_iff' measurableSet_cubeQ).2 (Eventually.of_forall fun Y hY => ?_)
    by_cases hK : Y ∈ Kset d N δ
    · have hYf : Y ∈ liftedFree d N := Kset_sub hψ.2.2.1 hK
      have hmem : (t0, Y) ∈ Ioo 0 T ×ˢ liftedFree d N := ⟨ht0, hYf⟩
      have hcg : ContinuousAt (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2)) (t0, Y) :=
        hgc.continuousAt (hO.mem_nhds hmem)
      have hc1 : ContinuousAt (fun t : ℝ => f t (mkC Y)) t0 :=
        hcg.comp (f := fun t : ℝ => (t, Y)) (x := t0) (continuous_id.prodMk continuous_const).continuousAt
      refine (continuousAt_const (y := ψ (mkC Y)) |>.mul hc1).congr ?_
      filter_upwards [Ioo_mem_nhds ht0.1 ht0.2] with t ht
      rw [ghat_of_mem (show (t, Y) ∈ Ioo 0 T ×ˢ liftedFree d N from ⟨ht, hYf⟩)]
      rfl
    · have : ∀ t, ψ (mkC Y) * ghat f T (t, Y) = 0 := fun t => by
        rw [vanish_off_Kset hψ hY hK, zero_mul]
      simp only [this]
      exact continuousAt_const

end HRS.MC.CepP4
