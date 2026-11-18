import HRS.Stochastic.Brownian

/-!
# S81R, packet R8: reweighting the initial law only

* `s81r_bf_withDensity`: if `(P, ℱ, W)` is a Brownian filtration, `g` is `ℱ₀`-measurable with `∫⁻ g dP = 1` and `g ≠ 0` a.e.,
  then `(P.withDensity g, ℱ, W)` is again a Brownian filtration (the increments stay independent of `ℱ_s`, Gaussian, and the
  null sets of `P.withDensity g` and `P` agree).
* `s81r_tv_bound`: total variation estimate `|E_{r(X₀)P} F - E_P F| ≤ ‖F‖_∞ · 2 (1 - c)` when `r ≥ c` a.e. under the law of `X₀`,
  `∫ r d law(X₀) = 1`.
* `s81r_bf_reindex`: a Brownian filtration stays one after a bijective reindexing of the coordinates.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HRS.MS.S81R

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- independence is preserved by a density measurable for the second sigma-algebra; the first sigma-algebra
sees the same measure -/
theorem s81r_indep_withDensity {Ω : Type*} {m1 m2 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h1 : m1 ≤ mΩ) (h2 : m2 ≤ mΩ) (hind : Indep m1 m2 P) {g : Ω → ℝ≥0∞} (hg : Measurable[m2] g)
    (hg1 : ∫⁻ ω, g ω ∂P = 1) :
    Indep m1 m2 (P.withDensity g) ∧ ∀ A, MeasurableSet[m1] A → P.withDensity g A = P A := by
  have key : ∀ A B, MeasurableSet[m1] A → MeasurableSet[m2] B →
      P.withDensity g (A ∩ B) = P A * P.withDensity g B := by
    intro A B hA hB
    have hA' : @MeasurableSet Ω mΩ A := h1 _ hA
    have hB' : @MeasurableSet Ω mΩ B := h2 _ hB
    have hgm : @Measurable Ω ℝ≥0∞ mΩ _ g := hg.mono h2 le_rfl
    rw [withDensity_apply _ (hA'.inter hB'), withDensity_apply _ hB', ← lintegral_indicator (hA'.inter hB'),
      ← lintegral_indicator hB']
    have e : ∀ ω, (A ∩ B).indicator g ω = A.indicator (fun _ => (1 : ℝ≥0∞)) ω * B.indicator g ω := by
      intro ω
      by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb, Set.indicator]
    simp_rw [e]
    rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace h1 h2 hind
      (measurable_const.indicator hA) (hg.indicator hB), lintegral_indicator hA']
    simp
  have key1 : ∀ A, MeasurableSet[m1] A → P.withDensity g A = P A := by
    intro A hA
    have := key A Set.univ hA MeasurableSet.univ
    rw [Set.inter_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1,
      mul_one] at this
    exact this
  refine ⟨?_, key1⟩
  rw [Indep_iff]
  intro A B hA hB
  rw [key A B hA hB, key1 A hA]

theorem s81r_bf_withDensity {ι : Type*} [Fintype ι] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W)
    {g : Ω → ℝ≥0∞} (hg : Measurable[ℱ 0] g) (hg1 : ∫⁻ ω, g ω ∂P = 1)
    (hpos : ∀ᵐ ω ∂P, g ω ≠ 0) : IsBrownianFiltration (P.withDensity g) ℱ W := by
  have hgm : Measurable g := hg.mono (ℱ.le 0) le_rfl
  have hac : P ≪ P.withDensity g := withDensity_absolutelyContinuous' hgm.aemeasurable hpos
  have hac' : P.withDensity g ≪ P := withDensity_absolutelyContinuous _ _
  haveI : IsProbabilityMeasure (P.withDensity g) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]
  have hint : ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (ℱ s) (P.withDensity g) ∧
      ∀ A, MeasurableSet[MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance] A →
        P.withDensity g A = P A := by
    intro s t hst
    have hmeas : Measurable (fun ω => W t ω - W s ω) :=
      ((hW.adapted t).mono (ℱ.le _) le_rfl).sub ((hW.adapted s).mono (ℱ.le _) le_rfl)
    exact s81r_indep_withDensity (P := P) hmeas.comap_le (ℱ.le s) (hW.indep_incr s t hst)
      (hg.mono (ℱ.mono s.coe_nonneg) le_rfl) hg1
  refine ⟨?_, hW.adapted, hW.zero, hW.cont, fun s t hst => (hint s t hst).1, fun s t hst => ?_⟩
  · intro t s hs h0
    exact hW.complete t s hs (hac h0)
  · have hmeas : Measurable (fun ω => W t ω - W s ω) :=
      ((hW.adapted t).mono (ℱ.le _) le_rfl).sub ((hW.adapted s).mono (ℱ.le _) le_rfl)
    refine ⟨hmeas.aemeasurable, ?_⟩
    have hP := (hW.gaussian_incr s t hst).map_eq
    rw [← hP]
    refine Measure.ext fun C hC => ?_
    rw [Measure.map_apply hmeas hC, Measure.map_apply hmeas hC]
    exact (hint s t hst).2 _ ⟨C, hC, rfl⟩

/-- reindexing the coordinates of a Brownian filtration -/
theorem s81r_bf_reindex {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W) :
    IsBrownianFiltration P ℱ (fun t ω k => W t ω (e.symm k)) := by
  have hg : Measurable (fun (v : ι → ℝ) (k : ι') => v (e.symm k)) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply (e.symm k)
  refine ⟨hW.complete, fun t => ?_, fun ω => ?_, fun ω => ?_, fun s t hst => ?_, fun s t hst => ?_⟩
  · exact hg.comp (hW.adapted t)
  · funext k
    simp [hW.zero ω]
  · exact continuous_pi fun k => (continuous_apply (e.symm k)).comp (hW.cont ω)
  · have h := hW.indep_incr s t hst
    refine indep_of_indep_of_le_left h ?_
    intro A hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact ⟨(fun (v : ι → ℝ) (k : ι') => v (e.symm k)) ⁻¹' C, hg hC, rfl⟩
  · have h := hW.gaussian_incr s t hst
    have hmp := measurePreserving_arrowCongr' (fun _ : ι => gaussianReal 0 (t - s))
      (fun _ : ι' => gaussianReal 0 (t - s)) e (MeasurableEquiv.refl ℝ)
      (fun i => MeasurePreserving.id _)
    have key : HasLaw ((⇑(MeasurableEquiv.arrowCongr' e (MeasurableEquiv.refl ℝ))) ∘
        (fun ω => W t ω - W s ω)) (Measure.pi fun _ : ι' => gaussianReal 0 (t - s)) P := by
      refine ⟨hmp.measurable.comp_aemeasurable h.aemeasurable, ?_⟩
      rw [← AEMeasurable.map_map_of_aemeasurable hmp.measurable.aemeasurable h.aemeasurable,
        h.map_eq]
      exact hmp.map_eq
    exact key

/-- total variation estimate for reweighting the initial law -/
theorem s81r_tv_bound {P : Measure Ω} [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E]
    {X0 : Ω → E} (hX : Measurable X0) (r : E → ℝ) (hr : Measurable r) (hr0 : ∀ x, 0 ≤ r x) {c : ℝ}
    (hc1 : c ≤ 1) (hrc : ∀ᵐ x ∂(P.map X0), c ≤ r x)
    (hint : ∫⁻ x, ENNReal.ofReal (r x) ∂(P.map X0) = 1) {F : Ω → ℝ} (hF : Measurable F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ ω, |F ω| ≤ C) :
    |∫ ω, F ω ∂(P.withDensity (fun ω => ENNReal.ofReal (r (X0 ω)))) - ∫ ω, F ω ∂P| ≤
      C * (2 * (1 - c)) := by
  set ν := P.map X0 with hν
  haveI : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  have hen : ∀ x, ‖r x‖ₑ = ENNReal.ofReal (r x) := fun x => Real.enorm_eq_ofReal (hr0 x)
  have hrint : Integrable r ν := by
    refine ⟨hr.aestronglyMeasurable, ?_⟩
    simp only [HasFiniteIntegral, hen]
    rw [hint]
    exact ENNReal.one_lt_top
  have hr1 : ∫ x, r x ∂ν = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hr0) hr.aestronglyMeasurable, hint]
    simp
  have hrX : Integrable (fun ω => r (X0 ω)) P := (integrable_map_measure hr.aestronglyMeasurable
    hX.aemeasurable).1 hrint
  have hgm : Measurable (fun ω => ENNReal.ofReal (r (X0 ω))) := (hr.comp hX).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hgm
    (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
  have htr : ∀ ω, (ENNReal.ofReal (r (X0 ω))).toReal = r (X0 ω) := fun ω =>
    ENNReal.toReal_ofReal (hr0 _)
  simp only [htr, smul_eq_mul]
  have hFi : Integrable F P := Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by simpa using hC ω)
  have hrF : Integrable (fun ω => r (X0 ω) * F ω) P := by
    refine Integrable.mono' (hrX.mul_const C) ((hr.comp hX).mul hF).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr0 _)]
    exact mul_le_mul_of_nonneg_left (hC ω) (hr0 _)
  rw [← integral_sub hrF hFi]
  have h1 : ∀ ω, r (X0 ω) * F ω - F ω = (r (X0 ω) - 1) * F ω := fun ω => by ring
  simp_rw [h1]
  refine (abs_integral_le_integral_abs).trans ?_
  have h2 : ∀ ω, |(r (X0 ω) - 1) * F ω| ≤ |r (X0 ω) - 1| * C := fun ω => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg _)
  have hmeas : Measurable (fun ω => |r (X0 ω) - 1|) := ((hr.comp hX).sub_const 1).abs
  have hint2 : Integrable (fun ω => |r (X0 ω) - 1|) P := (hrX.sub (integrable_const 1)).abs
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    (hint2.mul_const C) (Filter.Eventually.of_forall h2)).trans ?_
  rw [integral_mul_const]
  have h3 : ∫ ω, |r (X0 ω) - 1| ∂P = ∫ x, |r x - 1| ∂ν := by
    rw [hν, integral_map hX.aemeasurable]
    exact ((hr.sub_const 1).abs).aestronglyMeasurable
  have h4 : ∫ x, |r x - 1| ∂ν ≤ 2 * (1 - c) := by
    have hb : ∀ᵐ x ∂ν, |r x - 1| ≤ (r x - c) + (1 - c) := by
      filter_upwards [hrc] with x hx
      rw [abs_le]
      constructor <;> linarith
    have hi1 : Integrable (fun x => r x - c) ν := hrint.sub (integrable_const c)
    have hi : Integrable (fun x => (r x - c) + (1 - c)) ν := hi1.add (integrable_const _)
    have hi2 : Integrable (fun x => |r x - 1|) ν := (hrint.sub (integrable_const 1)).abs
    refine (integral_mono_ae hi2 hi hb).trans ?_
    have hcst : ∀ b : ℝ, ∫ _x, b ∂ν = b := fun b => by simp
    rw [integral_add hi1 (integrable_const _), integral_sub hrint (integrable_const c), hr1, hcst c,
      hcst (1 - c)]
    linarith
  rw [h3]
  calc (∫ x, |r x - 1| ∂ν) * C ≤ (2 * (1 - c)) * C := mul_le_mul_of_nonneg_right h4 hC0
    _ = C * (2 * (1 - c)) := by ring

end HRS.MS.S81R
