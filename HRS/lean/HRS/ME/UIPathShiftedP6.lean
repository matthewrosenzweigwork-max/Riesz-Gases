import HRS.ME.UIPath
import HRS.ME.UIPathShiftedQ5a
import HRS.ME.UIPathShiftedQ5b
import HRS.ME.UIPathTightP1

/-!
# Packet SQ6 of `HRS.ui_path_shifted`: assembly

Statement copied verbatim from `HRS/ME/UIPathShiftedSpec.lean` (sorried there, independently reviewed).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

/-- Assembly (statement of the frozen `HRS.ui_path_shifted`). -/
theorem p_assembly (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z) :
    TendstoInDistribution
      (fun n ω => windowGibbs m T (u n)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω)
      atTop (windowPath m T 0 Z) S.P P' := by
  have hm2 : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hprob : ∀ n, IsProbabilityMeasure
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) := by
    intro n
    have hGp : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (n + 2) β) :=
      HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
    unfold firstMarginal
    rw [dif_pos (by omega)]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_pi_apply _).aemeasurable).2 ‹_›
  have htight := shifted_family_tight hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT S hS hSF hν hUI m hm
    u hu0
  refine HRS.AdjK.adjk_convergence_of_tight_fidi_proof m T hT S.P
    (fun n ω => windowGibbs m T (u n)
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω) P'
    (windowPath m T 0 Z) ?_ ?_ htight ?_
  · intro n
    haveI := hprob n
    exact HRS.ME.UIPathTight.windowGibbs_aemeasurable (by omega) hm2 T (u n) _ (S.P n)
      (PDE.mfData d s hs0 hsd V β hβ) (u n + T) (S.X₀ n) (S.W n) (S.X n)
      (hS (u n + T) (add_nonneg (hu0 n) hT) n).sol
  · exact HRS.AdjK.adjk_toPath_aemeasurable_proof P' m T (fun t => Z (0 + t))
      (fun t => hZ.meas _) (by
        filter_upwards [hZ.cont] with ω hω
        refine ContinuousOn.comp hω (continuous_const.add continuous_id).continuousOn ?_
        intro t ht
        simpa using ht.1)
  · intro p ts hts φ hφ
    exact shifted_fidi_converge hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT S hS hSF hν hUI m hm u hu0 hu
      Ω' P' Z hZ p ts hts φ hφ

end HRS.ME.UIPathShifted
