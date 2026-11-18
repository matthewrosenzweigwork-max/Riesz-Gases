import HRS.MC.S7FCDefs

/-!
# FC-E packet, generic measurability lemmas (prefix `s7fcw12_`)

* `s7fcw12_measurable_of_edist`: Borel measurability of a map into a separable metric space from the
  measurability of all `edist (f ω) x`.
* `s7fcw12_measurable_ofSeq`: `ω ↦ NegSobolev.ofSeq m (c ω)` is measurable when every coordinate is.
* `s7fcw12_caratheodory`: a process continuous in `t` on `[0,T]` for a.e. `ω` and measurable in `ω` for each
  `t` has a jointly measurable version (modified on a null set).
* `s7fcw12_toL2_measurable`: `ω ↦ toL2 r T (F · ω)` is measurable for jointly measurable `F`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7FCW12

open HRS HRS.Sec7

/-- Borel measurability from measurability of the distance functions to a countable dense set. -/
theorem s7fcw12_measurable_of_edist {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
    [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E] (f : Ω → E)
    (h : ∀ x : E, Measurable fun ω => edist (f ω) x) : Measurable f := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  haveI : Countable D := hDc.to_subtype
  refine measurable_of_isOpen fun U hU => ?_
  have key : f ⁻¹' U = ⋃ (p : D × ℚ), ⋃ (_ : Metric.ball (p.1 : E) (p.2 : ℝ) ⊆ U ∧ 0 < (p.2 : ℝ)),
      {ω | edist (f ω) (p.1 : E) < ENNReal.ofReal (p.2 : ℝ)} := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_setOf_eq, exists_prop]
    constructor
    · intro hω
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (f ω) hω
      obtain ⟨x, hx, hxd⟩ := hDd.exists_dist_lt (f ω) (show 0 < ε / 3 by positivity)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ε / 3 < ε / 3 * 2 by linarith)
      have hsub : Metric.ball x (q : ℝ) ⊆ U := by
        intro y hy
        apply hball
        rw [Metric.mem_ball] at hy ⊢
        have h1 : dist y (f ω) ≤ dist y x + dist x (f ω) := dist_triangle _ _ _
        rw [dist_comm x (f ω)] at h1
        linarith
      have hq0 : (0 : ℝ) < q := by linarith
      refine ⟨(⟨x, hx⟩, q), ⟨hsub, hq0⟩, ?_⟩
      rw [edist_lt_ofReal]
      show dist (f ω) x < (q : ℝ)
      linarith
    · rintro ⟨⟨x, q⟩, ⟨hsub, _⟩, hlt⟩
      apply hsub
      rw [edist_lt_ofReal] at hlt
      exact Metric.mem_ball.2 hlt
  rw [key]
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (h _) measurable_const

/-- Square-summability of a real sequence through the `ℝ≥0∞`-valued sum. -/
theorem s7fcw12_summable_sq_iff {ι : Type*} (f : ι → ℝ) :
    Summable (fun k => f k ^ 2) ↔ ∑' k, ENNReal.ofReal (f k ^ 2) ≠ ⊤ := by
  constructor
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  · intro ht
    have := ENNReal.summable_toReal ht
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this

/-- The distance from an `ℓ²`-element to `x`, in terms of the coordinates, when the coordinates of `F` are
square-summable. -/
theorem s7fcw12_edist_eq {d : ℕ} {m : ℝ} (F x : NegSobolev d m) (hF : Summable fun k => (NegSobolev.coord F k) ^ 2) :
    edist F x = ENNReal.ofReal (Real.sqrt (∑' k, ENNReal.ofReal ((NegSobolev.coord F k - NegSobolev.coord x k) ^ 2)).toReal) := by
  have hcoord : ∀ k, NegSobolev.coord (F - x) k = NegSobolev.coord F k - NegSobolev.coord x k :=
    fun k => rfl
  have h1 := NegSobolev.coord_sq (F - x)
  simp only [hcoord] at h1
  have hs : Summable fun k => (NegSobolev.coord F k - NegSobolev.coord x k) ^ 2 := h1.1
  have hnn : 0 ≤ ∑' k, (NegSobolev.coord F k - NegSobolev.coord x k) ^ 2 := tsum_nonneg fun k => sq_nonneg _
  rw [edist_eq_enorm_sub, ← ofReal_norm_eq_enorm, ← Real.sqrt_sq (norm_nonneg _), h1.2,
    ← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hs, ENNReal.toReal_ofReal hnn]

/-- `ω ↦ ofSeq m (c ω)` is measurable when every coordinate is. -/
theorem s7fcw12_measurable_ofSeq {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {m : ℝ}
    (c : Ω → NonzeroLattice d → ℝ) (hc : ∀ k, Measurable fun ω => c ω k) :
    Measurable fun ω => NegSobolev.ofSeq m (c ω) := by
  set a : Ω → NonzeroLattice d → ℝ := fun ω k => Lattice.jp k.1 ^ (-m) * c ω k with ha
  have ha_meas : ∀ k, Measurable fun ω => a ω k := fun k => (hc k).const_mul _
  have hg : ∀ k, Measurable fun ω => ENNReal.ofReal (a ω k ^ 2) :=
    fun k => ENNReal.measurable_ofReal.comp ((ha_meas k).pow_const 2)
  have hsum : Measurable fun ω => ∑' k, ENNReal.ofReal (a ω k ^ 2) :=
    Measurable.ennreal_tsum hg
  set M : Set Ω := {ω | ∑' k, ENNReal.ofReal (a ω k ^ 2) ≠ ⊤} with hMdef
  have hM : MeasurableSet M := (measurableSet_singleton ⊤).compl.preimage hsum
  have hMmem : ∀ ω, ω ∈ M ↔ Memℓp (a ω) 2 := by
    intro ω
    rw [hMdef, mem_setOf_eq, Torus.memℓp_two_iff, s7fcw12_summable_sq_iff]
  have hzero : ∀ ω, ω ∉ M → NegSobolev.ofSeq m (c ω) = 0 := by
    intro ω hω
    unfold NegSobolev.ofSeq
    exact dif_neg (fun h => hω ((hMmem ω).2 h))
  -- on `M` the coordinates of `ofSeq` are `a ω`
  have hval : ∀ ω ∈ M, ∀ k, NegSobolev.coord (NegSobolev.ofSeq m (c ω)) k = a ω k := by
    intro ω hω k
    exact NegSobolev.coord_ofSeq_of_mem (c ω) ((hMmem ω).1 hω) k
  -- the distance functions
  refine s7fcw12_measurable_of_edist _ fun x => ?_
  let Φ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.sqrt
    (∑' k, ENNReal.ofReal ((a ω k - NegSobolev.coord x k) ^ 2)).toReal)
  have hΦ : Measurable Φ := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp (ENNReal.measurable_toReal.comp ?_))
    exact Measurable.ennreal_tsum fun k =>
      ENNReal.measurable_ofReal.comp (((ha_meas k).sub_const _).pow_const 2)
  have hfun : ∀ ω, edist (NegSobolev.ofSeq m (c ω)) x =
      if ω ∈ M then Φ ω else edist (0 : NegSobolev d m) x := by
    intro ω
    by_cases hω : ω ∈ M
    · rw [if_pos hω]
      have e : (fun k => (NegSobolev.coord (NegSobolev.ofSeq m (c ω)) k) ^ 2) = fun k => (a ω k) ^ 2 := by
        funext k
        rw [hval ω hω k]
      have hs : Summable fun k => (NegSobolev.coord (NegSobolev.ofSeq m (c ω)) k) ^ 2 := by
        rw [e]
        exact (s7fcw12_summable_sq_iff (a ω)).2 hω
      rw [s7fcw12_edist_eq _ x hs]
      simp only [Φ, hval ω hω]
    · rw [if_neg hω, hzero ω hω]
  have hmeas : Measurable fun ω => edist (NegSobolev.ofSeq m (c ω)) x := by
    simp only [hfun]
    exact Measurable.ite hM hΦ measurable_const
  exact hmeas

/-- Joint measurable versions: a process continuous in `t ∈ [0,T]` a.s. and measurable for each `t` agrees,
off a measurable null set, with a jointly measurable process on all of `ℝ × Ω`. -/
theorem s7fcw12_caratheodory {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (P : Measure Ω) {T : ℝ} (hT : 0 ≤ T) (u : ℝ → Ω → E) (hu : ∀ t, Measurable (u t))
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Set.Icc 0 T)) (e0 : E) :
    ∃ v : ℝ → Ω → E, Measurable (Function.uncurry v) ∧ ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω ∉ N, ∀ t ∈ Set.Icc (0 : ℝ) T, v t ω = u t ω := by
  classical
  set S : Set Ω := {ω | ¬ ContinuousOn (fun t => u t ω) (Set.Icc 0 T)} with hSdef
  have hS : P S = 0 := ae_iff.1 hc
  set N : Set Ω := toMeasurable P S with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable P S
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact hS
  have hcont : ∀ ω ∉ N, ContinuousOn (fun t => u t ω) (Set.Icc 0 T) := by
    intro ω hω
    by_contra hbad
    exact hω (subset_toMeasurable P S hbad)
  refine ⟨fun t ω => if ω ∈ N then e0 else u (Set.projIcc 0 T hT t) ω, ?_, N, hNm, hN0, ?_⟩
  · apply measurable_uncurry_of_continuous_of_measurable
    · intro ω
      by_cases hω : ω ∈ N
      · simp only [hω, ite_true]
        exact continuous_const
      · simp only [hω, ite_false]
        exact (hcont ω hω).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
          (fun t => (Set.projIcc 0 T hT t).2)
    · intro t
      exact Measurable.ite hNm measurable_const (hu _)
  · intro ω hω t ht
    simp only [hω, ite_false]
    rw [Set.projIcc_of_mem hT ht]

/-- The `L²(0,T;E)`-norm of a difference, for `Y` in `L²` and a strongly measurable representative `g` of `x`. -/
theorem s7fcw12_edist_toLp {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {Y : α → E} (hY : MemLp Y 2 μ) (x : Lp E 2 μ) (g : α → E) (hg : StronglyMeasurable g)
    (hxg : ⇑x =ᵐ[μ] g) :
    edist (hY.toLp Y) x = (∫⁻ a, ‖Y a - g a‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have h1 : ⇑(hY.toLp Y - x) =ᵐ[μ] Y - g :=
    (Lp.coeFn_sub _ _).trans ((MemLp.coeFn_toLp hY).sub hxg)
  rw [edist_eq_enorm_sub, Lp.enorm_def, eLpNorm_congr_ae h1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) (hY.aestronglyMeasurable.sub hg.aestronglyMeasurable)]
  simp

/-- `ω ↦ toL2 r T (F · ω)` is measurable for jointly measurable `F`. -/
theorem s7fcw12_toL2_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {r : ℝ} (T : ℝ)
    (F : ℝ → Ω → NegSobolev d r) (hF : Measurable (Function.uncurry F)) :
    Measurable fun ω => HRS.Sec7.toL2 r T (fun t => F t ω) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  have hsw : Measurable fun p : Ω × ℝ => F p.2 p.1 := hF.comp measurable_swap
  have hLint : Measurable fun p : Ω × ℝ => ‖F p.2 p.1‖ₑ ^ (2 : ℝ) := hsw.enorm.pow_const _
  have hI : Measurable fun ω => ∫⁻ t, ‖F t ω‖ₑ ^ (2 : ℝ) ∂μT := hLint.lintegral_prod_right'
  have hMmeas : MeasurableSet {ω | ∫⁻ t, ‖F t ω‖ₑ ^ (2 : ℝ) ∂μT < ⊤} := measurableSet_lt hI measurable_const
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  have hmem : ∀ ω, MemLp (fun t => F t ω) 2 μT ↔ ∫⁻ t, ‖F t ω‖ₑ ^ (2 : ℝ) ∂μT < ⊤ := by
    intro ω
    have hsm : AEStronglyMeasurable (fun t => F t ω) μT :=
      (Measurable.of_uncurry_right hF).aestronglyMeasurable
    have hiff : eLpNorm (fun t => F t ω) 2 μT < ⊤ ↔ ∫⁻ t, ‖F t ω‖ₑ ^ (2 : ℝ) ∂μT < ⊤ := by
      have := eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (μ := μT)
        (f := fun t => F t ω) (by norm_num) (by simp) hsm
      simpa using this
    exact hiff
  refine s7fcw12_measurable_of_edist _ fun x => ?_
  set g : ℝ → NegSobolev d r := (Lp.aestronglyMeasurable x).mk ⇑x with hgdef
  have hg' : StronglyMeasurable g := (Lp.aestronglyMeasurable x).stronglyMeasurable_mk
  have hg : Measurable g := hg'.measurable
  have hxg : ⇑x =ᵐ[μT] g := (Lp.aestronglyMeasurable x).ae_eq_mk
  have hΨ : Measurable fun ω => ∫⁻ t, ‖F t ω - g t‖ₑ ^ (2 : ℝ) ∂μT := by
    have hd : Measurable fun p : Ω × ℝ => F p.2 p.1 - g p.2 := hsw.sub (hg.comp measurable_snd)
    exact (hd.enorm.pow_const _).lintegral_prod_right'
  have key : (fun ω => edist (HRS.Sec7.toL2 r T (fun t => F t ω)) x) = fun ω =>
      if ∫⁻ t, ‖F t ω‖ₑ ^ (2 : ℝ) ∂μT < ⊤ then (∫⁻ t, ‖F t ω - g t‖ₑ ^ (2 : ℝ) ∂μT) ^ (1 / 2 : ℝ)
      else edist (0 : L2Path d r T) x := by
    funext ω
    by_cases h : ∫⁻ t, ‖F t ω‖ₑ ^ (2 : ℝ) ∂μT < ⊤
    · rw [if_pos h]
      unfold HRS.Sec7.toL2
      rw [dif_pos ((hmem ω).2 h)]
      exact s7fcw12_edist_toLp ((hmem ω).2 h) x g hg' hxg
    · rw [if_neg h]
      unfold HRS.Sec7.toL2
      rw [dif_neg (fun hh => h ((hmem ω).1 hh))]
  rw [key]
  exact Measurable.ite hMmeas (hΨ.pow_const _) measurable_const

end HRS.MC.Sec7.S7FCW12
