import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- `cond G A = G.withDensity (2 · 1_A)` when `G A = 1/2`. -/
theorem p_cp1_cond_eq {α : Type*} [MeasurableSpace α] (G : Measure α) {A : Set α} (hA : MeasurableSet A)
    (hGA : G A = 2⁻¹) :
    ProbabilityTheory.cond G A = G.withDensity (A.indicator (fun _ => (2 : ℝ≥0∞))) := by
  rw [withDensity_indicator hA, withDensity_const, ProbabilityTheory.cond, hGA, inv_inv]

theorem condou_weighted_integral (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) (T : ℝ) (hT : 0 ≤ T)
    {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (X₀₁ : Ω₁ → Config d N) (W₁ : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X₁ : ℝ≥0 → Ω₁ → Config d N)
    (hsel : SelectedFlow P₁ (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) T X₀₁ W₁ X₁)
    (hF₁ : ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace Ω₁))
      (W' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ), IsFilteredSolution P₁ ℱ W' W₁ X₁)
    {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (X₀₂ : Ω₂ → Config d N) (W₂ : ℝ≥0 → Ω₂ → (Fin N → Euc d)) (X₂ : ℝ≥0 → Ω₂ → Config d N)
    (h₂ : IsStationaryGibbsFlow P₂ s hs0 hsd (fun _ => (0 : ℝ)) β hβ T X₀₂ W₂ X₂)
    (A : Set (Config d N)) (hA : MeasurableSet A)
    (hGA : (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β A).toReal = 1 / 2)
    (hν : law P₁ X₀₁ = ProbabilityTheory.cond (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β) A)
    (F : Config d N → ℝ) (hF : Measurable F) (t : ℝ≥0) (ht : (t : ℝ) ≤ T) (f : ℝ →ᵇ ℝ) :
    ∫ ω, f (F (X₁ t ω)) ∂P₁ =
      ∫ ω, A.indicator (fun _ => (2 : ℝ)) (X₀₂ ω) * f (F (X₂ t ω)) ∂P₂ := by
  classical
  have hV : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := HRS.d1_isSmooth_const 0
  have : BorelSpace (Torus d) := Pi.borelSpace
  have : BorelSpace (Config d N) := Pi.borelSpace
  set G : Measure (Config d N) := canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β with hG
  have hGp : IsProbabilityMeasure G := HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  have hGA' : G A = 2⁻¹ := by
    have hfin : G A ≠ ∞ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin, hGA]
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hpart : IsParticleSystem P₁ (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) T X₀₁ W₁ X₁ := by
    refine ⟨hsel.brownian, hsel.indep, ?_⟩
    rcases hsel.flow with ⟨hs, -⟩ | ⟨hd1, -⟩
    · exact hs
    · exact absurd hd1 (by omega)
  have hcond : law P₁ X₀₁ = G.withDensity (A.indicator (fun _ => (2 : ℝ≥0∞))) := by
    rw [hν]; exact p_cp1_cond_eq G hA hGA'
  have hac : law P₁ X₀₁ ≪ G := by
    rw [hcond]; exact withDensity_absolutelyContinuous _ _
  have key := HRS.ME.Ret.ret_path_law_proof hd hs0 hsd (fun _ => (0 : ℝ)) hV hβ hN T hT P₁ X₀₁ W₁ X₁
    hpart hF₁ hac P₂ X₀₂ W₂ X₂ h₂
  set D : DynData d := PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ with hD
  have hstr₁ : IsStrongSolution P₁ D T X₀₁ W₁ X₁ := hpart.sol
  have hstr₂ : IsStrongSolution P₂ D T X₀₂ W₂ X₂ := by
    rcases h₂.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hX0₂ : ∀ᵐ ω ∂P₂, X₂ 0 ω = X₀₂ ω := hstr₂.init
  have hX₂0 : Measurable (X₂ 0) := hstr₂.adapted 0
  have hX₀₂m : AEMeasurable X₀₂ P₂ := hX₂0.aemeasurable.congr hX0₂
  have hpath₁ : Measurable fun ω => fun τ : {τ : ℝ≥0 // (τ : ℝ) ≤ T} => X₁ τ.1 ω :=
    measurable_pi_iff.2 fun τ => hstr₁.adapted τ.1
  have hpath₂ : Measurable fun ω => fun τ : {τ : ℝ≥0 // (τ : ℝ) ≤ T} => X₂ τ.1 ω :=
    measurable_pi_iff.2 fun τ => hstr₂.adapted τ.1
  set Φ₁ : Ω₁ → Config d N × ({τ : ℝ≥0 // (τ : ℝ) ≤ T} → Config d N) :=
    fun ω => (X₀₁ ω, fun τ : {τ : ℝ≥0 // (τ : ℝ) ≤ T} => X₁ τ.1 ω) with hΦ₁
  set Φ₂ : Ω₂ → Config d N × ({τ : ℝ≥0 // (τ : ℝ) ≤ T} → Config d N) :=
    fun ω => (X₀₂ ω, fun τ : {τ : ℝ≥0 // (τ : ℝ) ≤ T} => X₂ τ.1 ω) with hΦ₂
  have hΦ₁m : Measurable Φ₁ := hsel.init_meas.prodMk hpath₁
  have hΦ₂m : AEMeasurable Φ₂ P₂ := hX₀₂m.prodMk hpath₂.aemeasurable
  set Q : Measure (Config d N × ({τ : ℝ≥0 // (τ : ℝ) ≤ T} → Config d N)) := P₂.map Φ₂ with hQ
  set g : Config d N × ({τ : ℝ≥0 // (τ : ℝ) ≤ T} → Config d N) → ℝ :=
    fun z => f (F (z.2 ⟨t, ht⟩)) with hg
  have hgm : Measurable g :=
    f.continuous.measurable.comp (hF.comp ((measurable_pi_apply _).comp measurable_snd))
  set h2 : Config d N → ℝ≥0∞ := A.indicator (fun _ => (2 : ℝ≥0∞)) with hh2
  have hh2m : Measurable h2 := measurable_const.indicator hA
  have hQfst : Q.map Prod.fst = G := by
    rw [hQ, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hΦ₂m]
    exact (Measure.map_congr (Filter.Eventually.of_forall fun ω => rfl)).trans h₂.init
  have hrn : ∀ᵐ z ∂Q, (law P₁ X₀₁).rnDeriv G z.1 = h2 z.1 := by
    have hae : ∀ᵐ x ∂G, (law P₁ X₀₁).rnDeriv G x = h2 x := by
      rw [hcond]; exact Measure.rnDeriv_withDensity G hh2m
    have hae' : ∀ᵐ x ∂(Q.map Prod.fst), (law P₁ X₀₁).rnDeriv G x = h2 x := by
      rw [hQfst]; exact hae
    exact ae_of_ae_map measurable_fst.aemeasurable hae'
  have hlt : ∀ᵐ z ∂Q, h2 z.1 < ∞ := by
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [hh2, Set.indicator]
    split_ifs <;> simp
  have hL : ∫ ω, f (F (X₁ t ω)) ∂P₁ = ∫ z, g z ∂(Q.withDensity fun z => h2 z.1) := by
    have e : Q.withDensity (fun z => (law P₁ X₀₁).rnDeriv G z.1) = Q.withDensity fun z => h2 z.1 :=
      withDensity_congr_ae hrn
    rw [← e, ← key, integral_map hΦ₁m.aemeasurable hgm.aestronglyMeasurable]
  have hI : ∫ z, g z ∂(Q.withDensity fun z => h2 z.1) = ∫ z, (h2 z.1).toReal • g z ∂Q :=
    integral_withDensity_eq_integral_toReal_smul (hh2m.comp measurable_fst) hlt g
  have hgm2 : Measurable fun z : Config d N × ({τ : ℝ≥0 // (τ : ℝ) ≤ T} → Config d N) =>
      (h2 z.1).toReal • g z := (hh2m.comp measurable_fst).ennreal_toReal.smul hgm
  rw [hL, hI, hQ, integral_map hΦ₂m hgm2.aestronglyMeasurable]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hh2, hg, hΦ₂, smul_eq_mul, Set.indicator]
    split_ifs <;> simp

end HRS.MH.CondOuPackets

end
