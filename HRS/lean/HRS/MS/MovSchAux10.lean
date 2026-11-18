import HRS.MS.MovSchAux9

/-!
# S64 (S6.9), part 5: the dynamical parts of clauses (2) and (4)

Namespace `HRS.MS.MovSch`, prefix `s64_`.  A canonical particle solution `X` (`MovParticleSetup`) started from
`Q_{N,β}(T_{a_0}μ_*) = (ℙ_{N,β}).map (+a₀)` gives, by `movtr_strong_translate` with `-a₀`, the particle solution
`Y_t = X_t - a_t` (same Brownian motions) started from `X₀ - a₀`, which has law `ℙ_{N,β}`.
* `s64_ref2_dyn`: `GibbsInvariant` gives `law Y_t = ℙ_{N,β}`, hence `law X_t = ℙ_{N,β}.map(+a_t) = Q_{N,β}(T_{a_t}μ_*)`;
* `s64_ref4`: `GibbsEntropyContraction` and the data-processing inequality give the entropy comparison.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

section Dyn

variable {s q β : ℝ} {N : ℕ} {ρ₀ : Euc d → ℝ} {a₀ : Euc d} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}

lemma s64_aemeas_init (h : MovParticleSetup P d s q β N X₀ W X) : AEMeasurable X₀ P := by
  have h0 := h.sol 0
  exact ((h0.adapted 0).aemeasurable).congr (by filter_upwards [h0.init] with ζ hζ using hζ)

/-- The translated-back process. -/
def s64_Y (q : ℝ) (a₀ : Euc d) (X : ℝ≥0 → Ω → EucConfig d N) : ℝ≥0 → Ω → EucConfig d N :=
  fun t ζ i => X t ζ i + Real.exp (-q * (t : ℝ)) • (-a₀)

lemma s64_Y_eq (q : ℝ) (a₀ : Euc d) (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ≥0) :
    s64_Y q a₀ X t = fun ζ => (movtr_cfgEquiv d N (-movShift q a₀ (t : ℝ))) (X t ζ) := by
  funext ζ i
  simp [s64_Y, movtr_cfgEquiv_apply, movShift, smul_neg, sub_eq_add_neg]

lemma s64_X_eq (q : ℝ) (a₀ : Euc d) (X : ℝ≥0 → Ω → EucConfig d N) (t : ℝ≥0) :
    X t = fun ζ => (movtr_cfgEquiv d N (movShift q a₀ (t : ℝ))) (s64_Y q a₀ X t ζ) := by
  funext ζ i
  simp [s64_Y, movtr_cfgEquiv_apply, movShift, smul_neg]

lemma s64_Y_sol (hset : MovParticleSetup P d s q β N X₀ W X) (T : ℝ) :
    IsWholeStrongSolution P (quadraticGradientDyn d s q β) T (fun ζ i => X₀ ζ i + -a₀) W (s64_Y q a₀ X) :=
  movtr_strong_translate P s q β T X₀ W X (hset.sol T) (-a₀)

lemma s64_Y_meas (hset : MovParticleSetup P d s q β N X₀ W X) (t : ℝ≥0) : Measurable (s64_Y q a₀ X t) := by
  rw [s64_Y_eq]
  exact (movtr_cfgEquiv d N _).measurable.comp ((hset.sol t).adapted t)

lemma s64_movShift_zero (q : ℝ) (a₀ : Euc d) : movShift q a₀ 0 = a₀ := by simp [movShift]

/-- The law of `X₀ - a₀` is `ℙ_{N,β}` when `law X₀ = Q_{N,β}(T_{a_0} μ_*)`. -/
lemma s64_law_init (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β)
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ₀) (hN : 1 ≤ N)
    (hset : MovParticleSetup P d s q β N X₀ W X)
    (h0 : P.map X₀ = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ 0))) :
    P.map (fun ζ i => X₀ ζ i + -a₀) =
      HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β := by
  have hmeas := s64_aemeas_init hset
  have e1 : (fun ζ i => X₀ ζ i + -a₀) = (movtr_cfgEquiv d N (-a₀)) ∘ X₀ := by
    funext ζ i; simp [movtr_cfgEquiv_apply]
  rw [e1, ← AEMeasurable.map_map_of_aemeasurable (movtr_cfgEquiv d N (-a₀)).measurable.aemeasurable hmeas, h0]
  have h1 : movTranslatedDensity q a₀ ρ₀ 0 = fun x => ρ₀ (x - a₀) := by
    funext x; simp [movTranslatedDensity, movShift]
  rw [h1, s64_modGibbs_translate hs0 hq hβ hρ hN, s64_map_cancel]

theorem s64_ref2_dyn (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β)
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ₀) (hN : 1 ≤ N)
    (hInv : GibbsInvariant d s q β N) (hset : MovParticleSetup P d s q β N X₀ W X) [IsProbabilityMeasure P]
    (h0 : P.map X₀ = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ 0)))
    (t : ℝ) (ht : 0 ≤ t) :
    P.map (X t.toNNReal) = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ t)) := by
  have hlaw := s64_law_init hs0 hq hβ hρ hN hset h0
  have hindep : IndepFun (fun ζ i => X₀ ζ i + -a₀) (fun ζ t => W t ζ) P := by
    have := hset.indep.comp (movtr_cfgEquiv d N (-a₀)).measurable (measurable_id (α := ℝ≥0 → (Fin N → Euc d)))
    exact this
  have hcanon := hInv P t (fun ζ i => X₀ ζ i + -a₀) W (s64_Y q a₀ X) hset.brownian hindep hlaw
    (s64_Y_sol hset t) t.toNNReal (by rw [Real.coe_toNNReal _ ht])
  have hm := s64_Y_meas hset (a₀ := a₀) t.toNNReal
  have hX : X t.toNNReal = fun ζ => (movtr_cfgEquiv d N (movShift q a₀ ((t.toNNReal : ℝ≥0) : ℝ)))
      (s64_Y q a₀ X t.toNNReal ζ) := s64_X_eq q a₀ X _
  rw [Real.coe_toNNReal _ ht] at hX
  have e2 : movTranslatedDensity q a₀ ρ₀ t = fun x => ρ₀ (x - movShift q a₀ t) := rfl
  rw [e2, s64_modGibbs_translate hs0 hq hβ hρ hN, ← hcanon]
  rw [hX]
  exact (AEMeasurable.map_map_of_aemeasurable (movtr_cfgEquiv d N _).measurable.aemeasurable hm.aemeasurable).symm


theorem s64_ref4 (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β)
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ₀) (hN : 1 ≤ N)
    (hCon : GibbsEntropyContraction d s q β N) (hset : MovParticleSetup P d s q β N X₀ W X)
    [IsProbabilityMeasure P] (t : ℝ) (ht : 0 ≤ t) :
    HRS.relEntropy (P.map (X t.toNNReal)) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ t))) ≤
      HRS.relEntropy (P.map X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ 0))) := by
  haveI hprobc := s64_canon_prob (d := d) hs0 hq hβ hN
  have hindep : IndepFun (fun ζ i => X₀ ζ i + -a₀) (fun ζ t => W t ζ) P := by
    have := hset.indep.comp (movtr_cfgEquiv d N (-a₀)).measurable (measurable_id (α := ℝ≥0 → (Fin N → Euc d)))
    exact this
  have hC := hCon P t (fun ζ i => X₀ ζ i + -a₀) W (s64_Y q a₀ X) hset.brownian hindep
    (s64_Y_sol hset t) t.toNNReal (by rw [Real.coe_toNNReal _ ht])
  have hm := s64_Y_meas hset (a₀ := a₀) t.toNNReal
  haveI : IsProbabilityMeasure (P.map (s64_Y q a₀ X t.toNNReal)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hmeas0 := s64_aemeas_init hset
  haveI : IsProbabilityMeasure (P.map X₀) := (Measure.isProbabilityMeasure_map_iff hmeas0).2 inferInstance
  -- step 1
  have hX : X t.toNNReal = fun ζ => (movtr_cfgEquiv d N (movShift q a₀ ((t.toNNReal : ℝ≥0) : ℝ)))
      (s64_Y q a₀ X t.toNNReal ζ) := s64_X_eq q a₀ X _
  rw [Real.coe_toNNReal _ ht] at hX
  have e2 : movTranslatedDensity q a₀ ρ₀ t = fun x => ρ₀ (x - movShift q a₀ t) := rfl
  have e3 : P.map (X t.toNNReal) = (P.map (s64_Y q a₀ X t.toNNReal)).map (movtr_cfgEquiv d N (movShift q a₀ t)) := by
    rw [hX]
    exact (AEMeasurable.map_map_of_aemeasurable (movtr_cfgEquiv d N _).measurable.aemeasurable hm.aemeasurable).symm
  have step1 : HRS.relEntropy (P.map (X t.toNNReal)) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ t))) ≤
      HRS.relEntropy (P.map (s64_Y q a₀ X t.toNNReal))
        (HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β) := by
    rw [e2, s64_modGibbs_translate hs0 hq hβ hρ hN, e3]
    exact InformationTheory.klDiv_map_le _ _ (movtr_cfgEquiv d N _).measurable
  -- step 2
  have e4 : P.map (fun ζ i => X₀ ζ i + -a₀) = (P.map X₀).map (movtr_cfgEquiv d N (-a₀)) := by
    have e1 : (fun ζ i => X₀ ζ i + -a₀) = (movtr_cfgEquiv d N (-a₀)) ∘ X₀ := by
      funext ζ i; simp [movtr_cfgEquiv_apply]
    rw [e1]
    exact (AEMeasurable.map_map_of_aemeasurable (movtr_cfgEquiv d N (-a₀)).measurable.aemeasurable hmeas0).symm
  have h1 : movTranslatedDensity q a₀ ρ₀ 0 = fun x => ρ₀ (x - a₀) := by
    funext x; simp [movTranslatedDensity, movShift]
  have hmod0 := s64_modGibbs_translate hs0 hq hβ hρ hN a₀
  haveI : IsFiniteMeasure (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (fun x => ρ₀ (x - a₀)))) := by
    rw [hmod0]; infer_instance
  have step2 : HRS.relEntropy (P.map (fun ζ i => X₀ ζ i + -a₀))
        (HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β) ≤
      HRS.relEntropy (P.map X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (movTranslatedDensity q a₀ ρ₀ 0))) := by
    rw [h1, e4]
    conv_lhs => rw [← s64_map_cancel (HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s)
      (HRS.Whole.confinement q) N β) a₀, ← hmod0]
    exact InformationTheory.klDiv_map_le _ _ (movtr_cfgEquiv d N _).measurable
  exact step1.trans (hC.trans step2)

end Dyn

end HRS.MS.MovSch

end
