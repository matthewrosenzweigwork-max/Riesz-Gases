import HRS.ME.UIPath
import HRS.ME.RetPathLaw
import HRS.ME.RetGlueB
import HRS.MD.EQFrozen29Rest
import HRS.MD.EQLawPath
import HRS.Sections.AdjKGlue
import HRS.ME.UIPathTightP2
import HRS.ME.UIPathTightP3a
import HRS.MD.EQLawFlow

/-!
# Packet P3b of `HRS.ui_path_tight`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathTight

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- **P3b** (uniform tightness; statement copied verbatim from `UIPathTightSpec.lean`). -/
theorem stationary_window_tight_uniform (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ) (hT : 0 ≤ T) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set (PathSpace d m T), IsCompact K ∧
      ∀ (n : ℕ) (u : ℝ), 0 ≤ u →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d (n + 2)) (W : ℝ≥0 → Ω → (Fin (n + 2) → Euc d))
          (X : ℝ≥0 → Ω → Config d (n + 2)),
          IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X →
          (P.map (windowGibbs m T u
            (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) X)) Kᶜ ≤ ε := by
  classical
  have hmd : (d : ℝ) / 2 < m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    linarith
  have hm2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨Ω', _, P', _, Z, hZ⟩ := stationaryField_exists hd hs0 hsd hβ V hV ρβ hρβ m hm
  have hex : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (X₀ : Ω → Config d (n + 2))
      (W : ℝ≥0 → Ω → (Fin (n + 2) → Euc d)) (X : ℝ≥0 → Ω → Config d (n + 2)),
      IsStationaryGibbsFlow P s hs0 hsd V β hβ (0 + T) X₀ W X := fun n =>
    HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd V hV hβ (N := n + 2) (by omega) (0 + T)
      (by simpa using hT)
  choose Ω₂ inst P₂ hP₂ X₀₂ W₂ X₂ h₂ using hex
  letI : ∀ n, MeasurableSpace (Ω₂ n) := inst
  haveI : ∀ n, IsProbabilityMeasure (P₂ n) := hP₂
  have hconv := stationary_windows_converge hd hs0 hsd hβ V hV ρβ hρβ m hm T hT Ω₂ P₂ X₀₂ W₂ X₂
    h₂ Ω' P' Z hZ
  have htight := HRS.AdjK.adjk_tight_of_tendstoInDistribution hconv
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  intro ε hε
  obtain ⟨K, hK, hKε⟩ := htight ε hε
  refine ⟨K, hK, ?_⟩
  intro n u hu Ω _ P _ X₀ W X hX
  have h1 := windowGibbs_eq_windowZeta hd hs0 hsd hβ V hV (m := m) hm2
    T u hu (N := n + 2) (by omega) P X₀ W X hX
  have h2 := HRS.MD.EQLawPath.eq_path_stationary_proof hd hs0 hsd V hV hβ m hmd T hT
    (N := n + 2) (by omega) P X₀ W X u hu hX (P₂ n) (X₀₂ n) (W₂ n) (X₂ n) 0 le_rfl (h₂ n)
  rw [h1]
  have h3 : (P.map (Main.windowZeta m T u P X)) = (P₂ n).map (Main.windowZeta m T 0 (P₂ n) (X₂ n)) :=
    h2
  rw [h3]
  exact hKε _ ⟨n, rfl⟩

end HRS.ME.UIPathTight
