import HRS.Sections.AdjKGlueAux4
import HRS.Sections.AdjKGlueAux17

/-!
# ADJK-GLUE final: relocated proofs of `moving_integrated_forcing` (Lemma 5.8, third assertion) and
`dynamic_convergence` (Proposition 5.4, last paragraph); statements verbatim.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS

variable {d : ℕ}

theorem moving_integrated_forcing_proof (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ}
    {ρ : ℝ → Torus d → ℝ} (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (p₀ : ℝ) (hp₀ : 1 < p₀)
    (m : ℝ) (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        (∀ T' : ℝ, 0 ≤ T' → IsParticleSystem P htr.dyn T' X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        P.map X₀ ≪ modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0)) →
        eLpNorm ((P.map X₀).rnDeriv (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))))
          (ENNReal.ofReal p₀) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) < ⊤ →
        (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r =>
            Real.sqrt N * modulatedEnergy
              (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
              (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
        ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, ⨆ t ∈ {t : ℝ | t ∈ Set.Icc a (a + T) ∧ ∃ q : ℚ, (q : ℝ) = t}, ∑' k : NonzeroLattice d,
              ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
                evolvingForcingCoord htr.dyn ρ X k t ω ^ 2) ∂P ≤
            ENNReal.ofReal ((C * logMomentScale d s N p₀ (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) ^ 2) :=
  HRS.AdjK.adjkg_moving_integrated_forcing hd htr p₀ hp₀ m hm T hT

example := (@moving_integrated_forcing_proof : type_of% @HRS.moving_integrated_forcing)

theorem dynamic_convergence_proof (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) (S : ParticleSeq d)
    (hS : S.IsSolutionOn htr.dyn T)
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hfin : ∀ n, relEntropy ((S.P n).map (S.X₀ n))
      (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) ≠ ⊤)
    (hB : Tendsto (fun n : ℕ => entropyScale d s (n + 2) ((S.P n).map (S.X₀ n))
        (modulatedGibbs (periodicRiesz d s) (n + 2) β (withDensityReal (ρ 0))) /
          Real.sqrt ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0))
    (m : ℝ) (hm : (d : ℝ) + 4 < m)
    (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → NegSobolev d m)
    (hlaw : MeasureTheory.TendstoInDistribution
      (fun n ω => etaE m (S.X₀ n ω) (withDensityReal (ρ 0))) atTop η₀ S.P P')
    (Y : ℝ → Ω' → NegSobolev d m)
    (hY : IsLinearFluctuationSolution P' htr.dyn ρ m β⁻¹ T η₀ Y) :
    MeasureTheory.TendstoInDistribution
      (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (S.X n) ρ ω) atTop
      (toPath m T Y) S.P P' :=
  HRS.AdjK.adjkg_dynamic_convergence hd htr T hT S hS hSF hfin hB m hm Ω' P' η₀ hlaw Y hY

example := (@dynamic_convergence_proof : type_of% @HRS.dynamic_convergence)

end HRS
