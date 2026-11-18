import HRS.ME.RetGlueA
import HRS.ME.RetStmt
import HRS.ME.RetPathLaw

/-!
# Row 5.10: the comparisons of the glue of `ui_comparison`

* `ret_retVec_measurable`, `ret_propagator_continuous`: measurability of the vectors;
* `ret_window_compare`: the window of an arbitrary initial law is `d_{C²}`-close to the weighted stationary window,
  in terms of the `L¹(ℙ_{N,β})` distance of the densities (`ret_path_law_proof`);
* `ret_target_compare`: the same for the transported initial vector plus an independent Gaussian vector.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.MD HRS.MD.EQLawPath HRS.MD.EQLawFlow

variable {d : ℕ}

theorem ret_retVec_measurable (s β : ℝ) (V : Torus d → ℝ) (N : ℕ) {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Continuous (φ a)) : Measurable (retVec d s β V N φ) := by
  have : BorelSpace (Torus d) := Pi.borelSpace
  unfold retVec linCoord
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => ?_)
  refine Measurable.const_mul (Measurable.sub (Measurable.const_mul ?_ _) measurable_const) _
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (hφ a).measurable.comp ((measurable_pi_apply i).comp (measurable_pi_apply a))

theorem ret_propagator_continuous (D : DynData d) (ρ : ℝ → Torus d → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (φ : Torus d → ℝ) : Continuous (propagator D ρ 0 t φ) := by
  unfold propagator
  split_ifs with h
  · exact Torus.continuous_of_continuous_lift
      (show ContDiff ℝ 2 (Torus.lift (h.choose 0)) from h.choose_spec.c2 0 ⟨le_rfl, ht⟩).continuous
  · exact continuous_const

theorem ret_lintegral_fst_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (Q : Measure α)
    (γ : Measure β) [IsProbabilityMeasure γ] (g : α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g z.1 ∂(Q.prod γ) = ∫⁻ x, g x ∂Q := by
  have h : (Q.prod γ).map Prod.fst = Q := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← lintegral_map hg measurable_fst, h]

theorem ret_window_compare (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    (T : ℝ) (hT : 0 ≤ T) {p : ℕ} (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Continuous (φ a))
    (τ : Fin p → ℝ≥0) (hτ : ∀ a, (τ a : ℝ) ≤ T)
    {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (X₀₁ : Ω₁ → Config d N) (W₁ : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X₁ : ℝ≥0 → Ω₁ → Config d N)
    (h₁ : IsParticleSystem P₁ (PDE.mfData d s hs0 hsd V β hβ) T X₀₁ W₁ X₁)
    (hF₁ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω₁›)
      (W' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ), IsFilteredSolution P₁ ℱ W' W₁ X₁)
    (hac : law P₁ X₀₁ ≪ canonicalGibbs (periodicRiesz d s) V N β)
    {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (X₀₂ : Ω₂ → Config d N) (W₂ : ℝ≥0 → Ω₂ → (Fin N → Euc d)) (X₂ : ℝ≥0 → Ω₂ → Config d N)
    (h₂ : IsStationaryGibbsFlow P₂ s hs0 hsd V β hβ T X₀₂ W₂ X₂)
    (h' : Config d N → ℝ≥0∞) (hh' : Measurable h')
    (hint : ∫⁻ x, h' x ∂(canonicalGibbs (periodicRiesz d s) V N β) = 1) :
    ENNReal.ofReal (smoothDist 2
        (law P₁ fun ω => retVec d s β V N φ fun a => X₁ (τ a) ω)
        ((P₂.withDensity fun ω => h' (X₀₂ ω)).map
          fun ω => retVec d s β V N φ fun a => X₂ (τ a) ω)) ≤
      ∫⁻ x, (((law P₁ X₀₁).rnDeriv (canonicalGibbs (periodicRiesz d s) V N β) x - h' x) +
        (h' x - (law P₁ X₀₁).rnDeriv (canonicalGibbs (periodicRiesz d s) V N β) x)) ∂
          (canonicalGibbs (periodicRiesz d s) V N β) := by
  classical
  have : BorelSpace (Torus d) := Pi.borelSpace
  have : BorelSpace (Config d N) := Pi.borelSpace
  set G : Measure (Config d N) := canonicalGibbs (periodicRiesz d s) V N β with hG
  have hGp : IsProbabilityMeasure G := eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have key := ret_path_law_proof hd hs0 hsd V hV hβ hN T hT P₁ X₀₁ W₁ X₁ h₁ hF₁ hac P₂ X₀₂ W₂ X₂ h₂
  have hstr₁ : IsStrongSolution P₁ D T X₀₁ W₁ X₁ := h₁.sol
  have hstr₂ : IsStrongSolution P₂ D T X₀₂ W₂ X₂ := by
    rcases h₂.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hX0₁ : ∀ᵐ ω ∂P₁, X₁ 0 ω = X₀₁ ω := hstr₁.init
  have hX0₂ : ∀ᵐ ω ∂P₂, X₂ 0 ω = X₀₂ ω := hstr₂.init
  have hX₁0 : Measurable (X₁ 0) := hstr₁.adapted 0
  have hX₂0 : Measurable (X₂ 0) := hstr₂.adapted 0
  have hX₀₁m : AEMeasurable X₀₁ P₁ := hX₁0.aemeasurable.congr hX0₁
  have hX₀₂m : AEMeasurable X₀₂ P₂ := hX₂0.aemeasurable.congr hX0₂
  -- path maps
  have hpath₁ : Measurable fun ω => fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₁ t.1 ω :=
    measurable_pi_iff.2 fun t => hstr₁.adapted t.1
  have hpath₂ : Measurable fun ω => fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₂ t.1 ω :=
    measurable_pi_iff.2 fun t => hstr₂.adapted t.1
  set Φ₁ : Ω₁ → Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ T} → Config d N) :=
    fun ω => (X₀₁ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₁ t.1 ω) with hΦ₁
  set Φ₂' : Ω₂ → Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ T} → Config d N) :=
    fun ω => (X₂ 0 ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₂ t.1 ω) with hΦ₂'
  have hΦ₁m : AEMeasurable Φ₁ P₁ := hX₀₁m.prodMk hpath₁.aemeasurable
  have hΦ₂'m : Measurable Φ₂' := hX₂0.prodMk hpath₂
  have hJ₂ : P₂.map (fun ω => (X₀₂ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₂ t.1 ω)) =
      P₂.map Φ₂' := by
    refine Measure.map_congr ?_
    filter_upwards [hX0₂] with ω h0
    simp only [hΦ₂']
    rw [h0]
  rw [hJ₂] at key
  set h : Config d N → ℝ≥0∞ := (law P₁ X₀₁).rnDeriv G with hh
  have hhm : Measurable h := Measure.measurable_rnDeriv _ _
  -- the evaluation map
  set Fp : Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ T} → Config d N) → EuclideanSpace ℝ (Fin p) :=
    fun z => retVec d s β V N φ (fun a => z.2 ⟨τ a, hτ a⟩) with hFp
  have hFpm : Measurable Fp :=
    (ret_retVec_measurable s β V N φ hφ).comp
      (measurable_pi_iff.2 fun a => (measurable_pi_apply _).comp measurable_snd)
  -- the left law
  have e1 : law P₁ (fun ω => retVec d s β V N φ fun a => X₁ (τ a) ω) =
      ((P₂.map Φ₂').withDensity fun z => h z.1).map Fp := by
    calc law P₁ (fun ω => retVec d s β V N φ fun a => X₁ (τ a) ω) = P₁.map (Fp ∘ Φ₁) := rfl
      _ = (P₁.map Φ₁).map Fp :=
          (AEMeasurable.map_map_of_aemeasurable hFpm.aemeasurable hΦ₁m).symm
      _ = _ := by rw [show P₁.map Φ₁ = _ from key]
  have e2 : (P₂.withDensity fun ω => h' (X₀₂ ω)).map
        (fun ω => retVec d s β V N φ fun a => X₂ (τ a) ω) =
      ((P₂.map Φ₂').withDensity fun z => h' z.1).map Fp := by
    have c1 : (P₂.withDensity fun ω => h' (X₀₂ ω)) =
        P₂.withDensity (fun ω => h' ((Φ₂' ω).1)) :=
      withDensity_congr_ae (by filter_upwards [hX0₂] with ω h0; simp [hΦ₂', h0])
    have c2 : (P₂.withDensity fun ω => h' ((Φ₂' ω).1)).map Φ₂' =
        (P₂.map Φ₂').withDensity (fun z => h' z.1) :=
      ret_map_withDensity_fac P₂ Φ₂' Prod.fst hΦ₂'m measurable_fst h' hh'
    rw [c1]
    calc (P₂.withDensity fun ω => h' ((Φ₂' ω).1)).map
          (fun ω => retVec d s β V N φ fun a => X₂ (τ a) ω)
        = ((P₂.withDensity fun ω => h' ((Φ₂' ω).1)).map Φ₂').map Fp := by
          rw [Measure.map_map hFpm hΦ₂'m]; rfl
      _ = _ := by rw [c2]
  rw [e1, e2]
  set Q : Measure (Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ T} → Config d N)) := P₂.map Φ₂' with hQ
  have : IsProbabilityMeasure Q := inferInstance
  have hQfst : Q.map Prod.fst = G := by
    rw [hQ, Measure.map_map measurable_fst hΦ₂'m]
    have : (Prod.fst ∘ Φ₂') = X₂ 0 := rfl
    rw [this]
    calc P₂.map (X₂ 0) = P₂.map X₀₂ := Measure.map_congr hX0₂
      _ = G := h₂.init
  have hfin1 : IsFiniteMeasure (Q.withDensity fun z => h z.1) := by
    have : IsProbabilityMeasure (P₁.map Φ₁) := inferInstance
    rw [show Q.withDensity (fun z => h z.1) = P₁.map Φ₁ from key.symm]
    infer_instance
  have hfin2 : IsFiniteMeasure (Q.withDensity fun z => h' z.1) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← lintegral_map hh' measurable_fst, hQfst, hint]
    exact ENNReal.one_lt_top
  calc _ ≤ ∫⁻ z, ((h z.1 - h' z.1) + (h' z.1 - h z.1)) ∂Q :=
        ret_smoothDist_withDensity_le Q Fp hFpm (fun z => h z.1) (fun z => h' z.1)
          (hhm.comp measurable_fst) (hh'.comp measurable_fst)
    _ = _ := by
        rw [← lintegral_map (f := fun x => (h x - h' x) + (h' x - h x))
          ((hhm.sub hh').add (hh'.sub hhm)) measurable_fst, hQfst]

theorem ret_target_compare {α : Type*} [MeasurableSpace α] {p : ℕ} (G ν : Measure α)
    [IsProbabilityMeasure G] [IsProbabilityMeasure ν] (hac : ν ≪ G)
    (γ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure γ]
    (f : α → EuclideanSpace ℝ (Fin p)) (hf : Measurable f)
    (h' : α → ℝ≥0∞) (hh' : Measurable h') (hint : ∫⁻ x, h' x ∂G = 1) :
    ENNReal.ofReal (smoothDist 2 ((ν.map f) ∗ γ) (((G.withDensity h').map f) ∗ γ)) ≤
      ∫⁻ x, ((ν.rnDeriv G x - h' x) + (h' x - ν.rnDeriv G x)) ∂G := by
  have hhm : Measurable (ν.rnDeriv G) := Measure.measurable_rnDeriv _ _
  have hν : G.withDensity (ν.rnDeriv G) = ν := Measure.withDensity_rnDeriv_eq ν G hac
  set F : α × EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p) := fun z => f z.1 + z.2 with hF
  have hFm : Measurable F := (hf.comp measurable_fst).add measurable_snd
  have e1 : (ν.map f) ∗ γ =
      ((G.prod γ).withDensity fun z => ν.rnDeriv G z.1).map F := by
    rw [← ret_conv_withDensity G γ f hf _ hhm, hν]
  have e2 : ((G.withDensity h').map f) ∗ γ = ((G.prod γ).withDensity fun z => h' z.1).map F :=
    ret_conv_withDensity G γ f hf h' hh'
  have hfin1 : IsFiniteMeasure ((G.prod γ).withDensity fun z => ν.rnDeriv G z.1) := by
    rw [← prod_withDensity_left hhm, hν]; infer_instance
  have hGh : IsFiniteMeasure (G.withDensity h') := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hint]
    exact ENNReal.one_lt_top
  have hfin2 : IsFiniteMeasure ((G.prod γ).withDensity fun z => h' z.1) := by
    rw [← prod_withDensity_left hh']; infer_instance
  rw [e1, e2]
  calc _ ≤ ∫⁻ z, ((ν.rnDeriv G z.1 - h' z.1) + (h' z.1 - ν.rnDeriv G z.1)) ∂(G.prod γ) :=
        ret_smoothDist_withDensity_le (G.prod γ) F hFm (fun z => ν.rnDeriv G z.1)
          (fun z => h' z.1) (hhm.comp measurable_fst) (hh'.comp measurable_fst)
    _ = _ := ret_lintegral_fst_prod G γ (fun x => (ν.rnDeriv G x - h' x) + (h' x - ν.rnDeriv G x))
          ((hhm.sub hh').add (hh'.sub hhm))

/-- Image of a weighted initial datum, replacing the datum by an almost surely equal measurable one. -/
theorem ret_init_law {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (Y Y' : Ω → α) (hY' : Measurable Y') (hYY' : ∀ᵐ ω ∂P, Y' ω = Y ω)
    (g : α → ℝ≥0∞) (hg : Measurable g) (f : α → β) (hf : Measurable f) :
    (P.withDensity fun ω => g (Y ω)).map (fun ω => f (Y ω)) =
      ((P.map Y).withDensity g).map f := by
  have c1 : (P.withDensity fun ω => g (Y ω)) = P.withDensity (fun ω => g (id (Y' ω))) :=
    withDensity_congr_ae (by filter_upwards [hYY'] with ω h0; simp [h0])
  have c2 : (P.withDensity fun ω => g (id (Y' ω))).map Y' = (P.map Y').withDensity (fun z => g (id z)) :=
    ret_map_withDensity_fac P Y' id hY' measurable_id g hg
  have c3 : P.map Y' = P.map Y := Measure.map_congr hYY'
  have c4 : (P.withDensity fun ω => g (Y ω)).map (fun ω => f (Y ω)) =
      (P.withDensity fun ω => g (Y ω)).map (fun ω => f (Y' ω)) := by
    refine Measure.map_congr ?_
    exact (withDensity_absolutelyContinuous _ _).ae_le (by filter_upwards [hYY'] with ω h0; simp [h0])
  rw [c4, c1]
  calc (P.withDensity fun ω => g (id (Y' ω))).map (fun ω => f (Y' ω))
      = ((P.withDensity fun ω => g (id (Y' ω))).map Y').map f := by
        rw [Measure.map_map hf hY']; rfl
    _ = _ := by rw [c2, c3]; rfl

end HRS.ME.Ret

end
