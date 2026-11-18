import HRS.ME.UIPath
import HRS.ME.UIPathInitialR5
import HRS.ME.UIPathTightP1
import HRS.ME.UIPathTightP6

/-! Packet IR6: `p_assembly`. -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathInitial

open HRS HRS.Main

variable {d : ℕ}

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
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)))
      atTop η₀ S.P P')
    (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m β⁻¹ T η₀ Y) :
    TendstoInDistribution
      (fun n ω => windowGibbs m T 0
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω)
      atTop (toPath m T Y) S.P P' := by
  have hm2 : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have htight : IsTightMeasureSet (Set.range fun n => (S.P n).map (fun ω => windowGibbs m T 0
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω)) := by
    refine (HRS.ME.UIPathTight.p6_assembly hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT S hS hSF hν hUI
      m hm).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨n, 0, le_refl _, rfl⟩
  have hΦ : ∀ n, AEMeasurable (fun ω => windowGibbs m T 0
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.X n) ω) (S.P n) := by
    intro n
    haveI : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (n + 2) β) :=
      HRS.MD.EQLawFlow.eqlaw_gibbs_prob (by omega) hs0 hsd hV hβ (by omega)
    haveI : IsProbabilityMeasure
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) :=
      HRS.MD.EQTransShift.et_firstMarginal_isProb (by omega) _
    exact HRS.ME.UIPathTight.windowGibbs_aemeasurable (by omega : 1 ≤ n + 2) hm2 T 0
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (S.P n)
      (PDE.mfData d s hs0 hsd V β hβ) T (S.X₀ n) (S.W n) (S.X n) (hS T hT n).sol
  have hΨ : AEMeasurable (toPath m T Y) P' :=
    HRS.AdjK.adjk_toPath_aemeasurable_proof P' m T Y hY.meas hY.cont
  exact HRS.AdjK.adjk_convergence_of_tight_fidi_proof m T hT S.P _ P' (toPath m T Y) hΦ hΨ htight
    (fun p ts hts φ hφ => fidi_converges hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT S hS hSF hν hUI
      m hm Ω' P' η₀ hlaw Y hY p ts hts φ hφ)

end HRS.ME.UIPathInitial
