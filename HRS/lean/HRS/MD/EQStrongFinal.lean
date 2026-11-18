import HRS.MD.EQStrongFlow
import HRS.MD.EQStrongGauss
import HRS.MD.EQLZFinal

/-!
# EQ-STRONG: `eq_strong_moment_proof`

Flow clause: Lyons-Zheng with the Fourier coordinates as test functions (`eqstrong_flow_of_lz`, instantiated
with `HRS.MD.EQLZFinal.lyonsZheng_maximal_family_proof`).  Gaussian clause: coordinatewise dyadic chaining
(`eqstrong_gauss_clause`), not routed through `HRS.Uniform.MaxWindows`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQStrong

open HRS.LZ HRS.MD.EQ29

variable {d : ℕ}

theorem eq_strong_moment_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m q : ℝ) (hq : (d : ℝ) / 2 + 1 < q) (hqm : q < m) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      (∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsStationaryGibbsFlow P s hs0 hsd V β (hβm.trans_le hβ.1) (u + T) X₀ W X →
          ∫⁻ ω, ⨆ t ∈ ratTimes u T, coordEnergy q (fun k => NegSobolev.fourierCoeff
              (zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)) k) ∂P ≤ ENNReal.ofReal C) ∧
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, coordEnergy q (fun k => NegSobolev.fourierCoeff (Z t ω) k) ∂P' ≤
          ENNReal.ofReal C := by
  obtain ⟨C1, hC1, h1⟩ := eqstrong_flow_of_lz HRS.MD.EQLZFinal.lyonsZheng_maximal_family_proof hd
    hs0 hsd V hV βm βp hβm hββ m q hq hqm T hT
  obtain ⟨C2, hC2, h2⟩ := eqstrong_gauss_clause hd hs0 hsd V hV βm hβm m q hq T hT
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro β hβ ρβ hρ
  refine ⟨?_, ?_⟩
  · intro u hu N hN Ω _ P _ X₀ W X hflow
    exact (h1 β hβ ρβ hρ u hu N hN P X₀ W X hflow).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  · intro Ω' _ P' _ Z hZ
    exact (h2 β hβ.1 ρβ hρ P' Z hZ).trans (ENNReal.ofReal_le_ofReal (by linarith))

end HRS.MD.EQStrong
