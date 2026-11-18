import HRS.Uniform.Comparison
import HRS.Uniform.Evolution
import HRS.MD.EQEvoLevel
import HRS.Uniform.Q48eAux1
import HRS.Main.T25MWAux1

/-!
# EQP7E: final assembly of the stationary dual evolution, `eq_evolution_uniform_proof` (packets P7.8-P7.10)

* P7.7 (`eqevo_level_stat`, proved in `HRS.MD.EQEvoLevel`) gives, uniformly in `β ∈ [βm, βp]` and thermal `ρβ`, a dual
  evolution `Vev` with exponential growth rate `c` and decay `Cr e^{-cr (t-u)}`. Its proof is
  `HRS.MD.EQEvoLevel.eqevo_level_stat_proof`.
* P7.8 (`MaxWindows`) and P7.9 (stochastic convolution, continuity, measurability) are both read off `winmax_of_quasi`
  (window maximal estimate for a quasi-contractive evolution, rate `2c`) and `t25mw_maxWindows_of_winMaxU`.
* The constants before `β` are `K := Cr`, `c := cr`, `Cmax := Kot.CD 2 (2c) T`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Uniform

namespace HRS.MD.EQEvoFinal

variable {d : ℕ}

/-- Final assembly (packet `eq_evolution_uniform`): statement verbatim from `HRS/MD/EQ29Spec.lean`. -/
theorem eq_evolution_uniform_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (M : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K c Cmax : ℝ, 0 ≤ K ∧ 0 < c ∧ 0 ≤ Cmax ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∃ Vev : ℝ → ℝ → NegSobolev d M →L[ℝ] NegSobolev d M,
        IsDualEvolution (PDE.mfData d s hs0 hsd V β (hβm.trans_le hβ.1)) (fun _ => ρβ) M Vev ∧
        (∀ T' : ℝ, 0 ≤ T' → IsPlainEvolution Vev T') ∧
        (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ K * Real.exp (-c * (t - u))) ∧
        MaxWindows.{0, 0} Vev T Cmax ∧
        ∀ S : ℝ, 0 ≤ S → ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (ℱ : Filtration ℝ mΩ) (Mart : ℝ → Ω → NegSobolev d M)
          (Sg : ℝ → Ω → (NegSobolev d M →L[ℝ] NegSobolev d M →L[ℝ] ℝ)),
          IsHilbertMartingaleWithCovariation P ℱ S Mart Sg →
          ∃ Z : ℝ → Ω → NegSobolev d M,
            (∀ t ∈ Set.Icc (0 : ℝ) S,
              IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d M)) Mart 0 t (Z t)) ∧
            (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 S)) ∧
            ∀ t ∈ Set.Icc (0 : ℝ) S, AEMeasurable (Z t) P := by
  obtain ⟨c, Cr, cr, hCr, hcr, hL⟩ := HRS.MD.EQEvoLevel.eqevo_level_stat_proof hd hs0 hsd V hV βm βp hβm hββ M
  refine ⟨Cr, cr, Kot.CD 2 (2 * c) T, hCr.le, hcr, Kot.CD_nonneg _ _ _, ?_⟩
  intro β hβ ρβ hρβ
  obtain ⟨Vev, hdual, hplain, hgrow, hdec⟩ := hL β hβ ρβ hρβ
  have hq : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp ((2 * c) * (t - u) / 2) := by
    intro u t hu hut
    rw [show (2 * c) * (t - u) / 2 = c * (t - u) by ring]
    exact hgrow u t hu hut
  refine ⟨Vev, hdual, hplain, hdec, ?_, ?_⟩
  · exact HRS.T25MW.t25mw_maxWindows_of_winMaxU
      (HRS.Uniform.Q48e.winmax_of_quasi.{0} hplain (K := 2 * c) hq hT)
  · intro S hS Ω mΩ P _ ℱ Mart Sg hM
    have hW := HRS.Uniform.Q48e.winmax_of_quasi.{0} hplain (K := 2 * c) hq hS
    obtain ⟨Z, h1, h2, h3, -⟩ := hW Ω P ℱ 0 le_rfl Mart Sg (by rw [zero_add]; exact hM)
    rw [zero_add] at h1 h2 h3
    exact ⟨Z, h1, h3, fun t ht => (h2 t ht).aemeasurable⟩

end HRS.MD.EQEvoFinal

end
