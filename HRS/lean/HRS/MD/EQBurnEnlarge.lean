import HRS.MD.EQBurnDefs
import HRS.MD.EQLawFlow
import HRS.Main.T25PAux1
import HRS.Main.T25PAux21

/-!
# Packet EQ-BURN P3 (chunk D): `eq_enlarge_proof`

Relocated proof of `HRS.MD.EQBurn.eq_enlarge` (frozen with its `sorry` in `HRS/MD/EQBurnSpec.lean`; the tie
`HRS/MD/EQBurnEnlargeTie.lean` checks that the statements agree).  Route: `t25p_init_enlargement` with the constant kernel `ν₀`,
then `IsStationaryGibbsFlow` is transferred field by field along the projection; `PathwiseUnique` is re-derived on the enlarged space
from `particle_wellposed_proof` (`T > 0`) and is trivial at `T = 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQBurnEnlarge

open HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- Transfer of `IsStationaryGibbsFlow` along a measure preserving map. -/
theorem eqenl_gibbs_comp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω Ω' : Type} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {π : Ω' → Ω} (hπ : MeasurePreserving π P' P)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X)
    {ℱ' : Filtration ℝ mΩ'} {W'' : ℝ≥0 → Ω' → (Fin N × Fin d) → ℝ}
    (hF' : IsFilteredSolution P' ℱ' W'' (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω'))) :
    IsStationaryGibbsFlow P' s hs0 hsd V β hβ T (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω'))
      (fun t ω' => X t (π ω')) := by
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hV2 : Torus.IsCk 2 D.V :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hM : Torus.SymNonpos D.M := EQLawFlow.eqlaw_symNonpos_neg_one
  have hsel := hX.flow
  have hstr : IsStrongSolution P D T X₀ W X := by
    rcases hsel.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hPS : IsParticleSystem P D T X₀ W X := ⟨hsel.brownian, hsel.indep, hstr⟩
  have hPS' := HRS.T25P.t25p_isParticleSystem_comp hπ hPS
  have hmeas' : Measurable (fun ω' => X₀ (π ω')) := hsel.init_meas.comp hπ.measurable
  have hdist' : ∀ᵐ ω' ∂P', X₀ (π ω') ∉ collisionSet d N :=
    hπ.quasiMeasurePreserving.ae hsel.init_distinct
  refine ⟨⟨hmeas', hdist', hPS'.brownian, hPS'.indep, Or.inl ⟨hPS'.sol, ?_⟩⟩, ⟨ℱ', W'', hF'⟩, ?_⟩
  · intro X1 X2 h1 h2
    rcases lt_or_eq_of_le hT with hT0 | hT0
    · exact (particle_wellposed_proof P' D hd hN hM hV2 _ hmeas' hdist' _ hPS'.brownian hPS'.indep T hT0).2
        X1 X2 h1 h2
    · filter_upwards [h1.init, h2.init] with ω' e1 e2 t ht
      have : t = 0 := by
        have h0 : (t : ℝ) ≤ 0 := by rw [← hT0] at ht; exact ht
        exact NNReal.coe_eq_zero.1 (le_antisymm h0 t.2)
      subst this
      rw [e1, e2]
  · have e : P'.map (fun ω' => X₀ (π ω')) = P.map X₀ := by
      conv_rhs => rw [← hπ.map_eq]
      exact (Measure.map_map hsel.init_meas hπ.measurable).symm
    exact e.trans hX.init

theorem eq_enlarge_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (m : ℝ)
    (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (ν₀ : Measure (NegSobolev d m)) [IsProbabilityMeasure ν₀] :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (W'' : ℝ≥0 → Ω' → (Fin N × Fin d) → ℝ) (η' : Ω' → NegSobolev d m),
      IsStationaryGibbsFlow P' s hs0 hsd V β hβ T (fun ω' => X₀ (π ω')) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      IsFilteredSolution P' ℱ' W'' (fun t ω' => W t (π ω')) (fun t ω' => X t (π ω')) ∧
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      Measurable[ℱ' 0] η' ∧
      P'.map (fun ω' => (X₀ (π ω'), η' ω')) = (P.map X₀).prod ν₀ := by
  have hstr : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) T X₀ W X := by
    rcases hX.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', η', h1, h2, h3, h4⟩ :=
    HRS.T25P.t25p_init_enlargement m N P X₀ W X ℱ W' hF hstr.init (Kernel.const _ ν₀)
  refine ⟨Ω', mΩ', P', hP', π, hπ, ℱ', _, η', ?_, h2, h1, h3, ?_⟩
  · exact eqenl_gibbs_comp hd hs0 hsd V hV hβ T hT hN hπ hX h2
  · rw [h4, Measure.compProd_const]

end EQBurnEnlarge

end MD

end HRS
