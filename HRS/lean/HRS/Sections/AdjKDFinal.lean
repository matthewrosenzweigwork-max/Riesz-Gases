import HRS.Sections.AdjKDAux1
import HRS.Sections.AdjKDAux2
import HRS.Sections.AdjKDAux3
import HRS.Sections.AdjKDAux8

/-!
# ADJKD final: relocated proofs of `AdjKSpec` packets M0a, M0b, F, B2 (statements verbatim)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjk_flucPath_aemeasurable_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 < m) (T : ℝ) (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) :
    AEMeasurable (fun ω => flucPath m T (Real.sqrt N) X ρ ω) P :=
  adjkd_flucPath_aemeasurable hd htr m hm T hT hN P X₀ W X hX

example := (@adjk_flucPath_aemeasurable_proof : type_of% @HRS.AdjK.adjk_flucPath_aemeasurable)

theorem adjk_toPath_aemeasurable_proof {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (m T : ℝ)
    (Y : ℝ → Ω → NegSobolev d m) (hmeas : ∀ t, Measurable (Y t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (toPath m T Y) P :=
  adjkd_toPath_aemeasurable P m T Y hmeas hcont

example := (@adjk_toPath_aemeasurable_proof : type_of% @HRS.AdjK.adjk_toPath_aemeasurable)

theorem adjk_convergence_of_tight_fidi_proof (m T : ℝ) (hT : 0 ≤ T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Φ : ∀ n, Ω n → PathSpace d m T)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ψ : Ω' → PathSpace d m T) (hΦ : ∀ n, AEMeasurable (Φ n) (P n)) (hΨ : AEMeasurable Ψ P')
    (htight : IsTightMeasureSet (Set.range fun n => (P n).map (Φ n)))
    (hfidi : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
      (φ : Fin p → Torus d → ℝ), (∀ a, Torus.IsSmooth (φ a)) →
      TendstoInDistribution
        (fun n ω => (WithLp.toLp 2 fun a => NegSobolev.eval ((Φ n ω).at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
        atTop
        (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval ((Ψ ω').at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
        P P') :
    TendstoInDistribution Φ atTop Ψ P P' :=
  adjkd_convergence_of_tight_fidi m T hT P Φ P' Ψ hΦ hΨ htight hfidi

example := (@adjk_convergence_of_tight_fidi_proof : type_of% @HRS.AdjK.adjk_convergence_of_tight_fidi)

theorem adjk_remainder_L1_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
          IntervalIntegrable (fun r =>
            Real.sqrt N * modulatedEnergy
              (commKernel (periodicRieszGrad d htr.dyn.s)
                (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
              (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
        ∫⁻ ω, ⨆ t ∈ ratIcc 0 T, (∑' k : NonzeroLattice d,
            ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) * evolvingForcingCoord htr.dyn ρ X k t ω ^ 2)) ^
              (1 / 2 : ℝ) ∂P ≤
          ENNReal.ofReal (C * entropyScale d s N (P.map X₀)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N) :=
  adjkd_remainder_L1 hd htr m hm T hT

example := (@adjk_remainder_L1_proof : type_of% @HRS.AdjK.adjk_remainder_L1)

end HRS.AdjK
