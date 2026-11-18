import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue
import HRS.ME.UIPathTightP1
import HRS.ME.UIPathTightP4

/-! Packet UP5: `ret_window_tail`. -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}


/-- **P5** (the transfer inequality `ν(A) ≤ Θ(L) + L λ(A)`; scope note 1.1 step 3).  Let `P₁` be a filtered
particle system with `N` particles on the horizon `u + T` whose initial law is `≪ ℙ_{N,β}`, and `P₂` a stationary
Gibbs flow on the same horizon.  Then for every measurable set `A` of windows and every `L ≥ 0`, the law of the
Gibbs-centred window under `P₁` satisfies
`≤ ν{h > L} + L · (law of the Gibbs-centred window under P₂)(A)`, `ν = law P₁ X₀₁`, `h = dν/dℙ_{N,β}`.
(Stated for a single `N`; `ν{h > L} ≤ uiTail L` is `le_iSup` in P6.)  Route: P1, P4, `ret_path_law_proof`
(template `RetGlueB.lean:94-137`), split `h ≤ L` / `h > L`, `Measure.withDensity_rnDeriv_eq`. -/
theorem ret_window_tail (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (T : ℝ) (hT : 0 ≤ T) (u : ℝ) (hu : 0 ≤ u) {N : ℕ} (hN : 2 ≤ N)
    {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (X₀₁ : Ω₁ → Config d N) (W₁ : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X₁ : ℝ≥0 → Ω₁ → Config d N)
    (h₁ : IsParticleSystem P₁ (PDE.mfData d s hs0 hsd V β hβ) (u + T) X₀₁ W₁ X₁)
    (hF₁ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω₁›)
      (W' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ), IsFilteredSolution P₁ ℱ W' W₁ X₁)
    (hac : law P₁ X₀₁ ≪ canonicalGibbs (periodicRiesz d s) V N β)
    {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (X₀₂ : Ω₂ → Config d N) (W₂ : ℝ≥0 → Ω₂ → (Fin N → Euc d)) (X₂ : ℝ≥0 → Ω₂ → Config d N)
    (h₂ : IsStationaryGibbsFlow P₂ s hs0 hsd V β hβ (u + T) X₀₂ W₂ X₂)
    (A : Set (PathSpace d m T)) (hA : MeasurableSet A) (L : ℝ) (hL : 0 ≤ L) :
    (P₁.map (windowGibbs m T u (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X₁)) A ≤
      (law P₁ X₀₁) {x | ENNReal.ofReal L <
        (law P₁ X₀₁).rnDeriv (canonicalGibbs (periodicRiesz d s) V N β) x} +
      ENNReal.ofReal L *
        (P₂.map (windowGibbs m T u (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X₂)) A := by
  
  classical
  have : BorelSpace (Torus d) := Pi.borelSpace
  have : BorelSpace (Config d N) := Pi.borelSpace
  set G : Measure (Config d N) := canonicalGibbs (periodicRiesz d s) V N β with hG
  have hGp : IsProbabilityMeasure G := HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  haveI hμp : IsProbabilityMeasure (firstMarginal G) := by
    unfold firstMarginal
    rw [dif_pos (by omega)]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 ‹_›
  set μ : Measure (Torus d) := firstMarginal G with hμ
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hTu : 0 ≤ u + T := by linarith
  have key := HRS.ME.Ret.ret_path_law_proof hd hs0 hsd V hV hβ hN (u + T) hTu P₁ X₀₁ W₁ X₁ h₁ hF₁ hac
    P₂ X₀₂ W₂ X₂ h₂
  have hstr₁ : IsStrongSolution P₁ D (u + T) X₀₁ W₁ X₁ := h₁.sol
  have hstr₂ : IsStrongSolution P₂ D (u + T) X₀₂ W₂ X₂ := by
    rcases h₂.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  obtain ⟨B, hBm, hB⟩ := ret_window_event (d := d) (N := N) (by omega) hm T u hu μ A hA
  have hB₁ := hB P₁ X₀₁ X₁ hstr₁.adapted hstr₁.cont
  have hB₂ := hB P₂ X₀₂ X₂ hstr₂.adapted hstr₂.cont
  have hw₁ : AEMeasurable (windowGibbs m T u μ X₁) P₁ :=
    windowGibbs_aemeasurable (by omega) hm T u μ P₁ D (u + T) X₀₁ W₁ X₁ hstr₁
  have hw₂ : AEMeasurable (windowGibbs m T u μ X₂) P₂ :=
    windowGibbs_aemeasurable (by omega) hm T u μ P₂ D (u + T) X₀₂ W₂ X₂ hstr₂
  have hX₀₁m : AEMeasurable X₀₁ P₁ := (hstr₁.adapted 0).aemeasurable.congr hstr₁.init
  have hX₀₂m : AEMeasurable X₀₂ P₂ := (hstr₂.adapted 0).aemeasurable.congr hstr₂.init
  have hpath₁ : Measurable fun ω => fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X₁ t.1 ω :=
    measurable_pi_iff.2 fun t => hstr₁.adapted t.1
  have hpath₂ : Measurable fun ω => fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X₂ t.1 ω :=
    measurable_pi_iff.2 fun t => hstr₂.adapted t.1
  set J₁ : Ω₁ → Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ u + T} → Config d N) :=
    fun ω => (X₀₁ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X₁ t.1 ω) with hJ₁
  set J₂ : Ω₂ → Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ u + T} → Config d N) :=
    fun ω => (X₀₂ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ u + T} => X₂ t.1 ω) with hJ₂
  have hJ₁m : AEMeasurable J₁ P₁ := hX₀₁m.prodMk hpath₁.aemeasurable
  have hJ₂m : AEMeasurable J₂ P₂ := hX₀₂m.prodMk hpath₂.aemeasurable
  set Q := P₂.map J₂ with hQ
  set ν : Measure (Config d N) := law P₁ X₀₁ with hν
  set h : Config d N → ℝ≥0∞ := ν.rnDeriv G with hh
  have hhm : Measurable h := Measure.measurable_rnDeriv _ _
  have hQfst : Q.map Prod.fst = G := by
    rw [hQ, AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hJ₂m]
    exact h₂.init
  set S : Set (Config d N) := {x | ENNReal.ofReal L < h x} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hhm
  have hνS : ∫⁻ x in S, h x ∂G = ν S := by
    rw [← withDensity_apply _ hSm, hh, Measure.withDensity_rnDeriv_eq ν G hac]
  have e1 : (P₁.map (windowGibbs m T u μ X₁)) A = (P₁.map J₁) B := by
    rw [Measure.map_apply_of_aemeasurable hw₁ hA, Measure.map_apply_of_aemeasurable hJ₁m hBm]
    exact measure_congr hB₁
  have e2 : (P₂.map (windowGibbs m T u μ X₂)) A = Q B := by
    rw [Measure.map_apply_of_aemeasurable hw₂ hA, hQ,
      Measure.map_apply_of_aemeasurable hJ₂m hBm]
    exact measure_congr hB₂
  rw [e1, e2, key, withDensity_apply _ hBm]
  calc ∫⁻ z in B, h z.1 ∂Q
      ≤ ∫⁻ z in B, (ENNReal.ofReal L + S.indicator h z.1) ∂Q := by
        refine lintegral_mono fun z => ?_
        by_cases hz : z.1 ∈ S
        · rw [Set.indicator_of_mem hz]; exact le_add_self
        · rw [Set.indicator_of_notMem hz, add_zero]
          exact not_lt.1 hz
    _ = ENNReal.ofReal L * Q B + ∫⁻ z in B, S.indicator h z.1 ∂Q := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ ≤ ENNReal.ofReal L * Q B + ν S := by
        gcongr
        calc ∫⁻ z in B, S.indicator h z.1 ∂Q ≤ ∫⁻ z, S.indicator h z.1 ∂Q :=
              lintegral_mono' Measure.restrict_le_self le_rfl
          _ = ∫⁻ x, S.indicator h x ∂G := by
              rw [← hQfst, lintegral_map (hhm.indicator hSm) measurable_fst]
          _ = ν S := by rw [lintegral_indicator hSm, hνS]
    _ = ν S + ENNReal.ofReal L * Q B := add_comm _ _
