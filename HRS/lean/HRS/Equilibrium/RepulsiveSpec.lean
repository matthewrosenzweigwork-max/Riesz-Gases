/-
# HRS.Equilibrium.RepulsiveSpec — package REP-07: the uniform partition-function bound

Endpoint of the packages REP-00 … REP-06: the torus version of DGR Theorem 2.2(i) for the
periodic logarithm, `sup_{N ≥ 2, 0 ≤ γ ≤ B₀} K_{N,γ}(μ) < ∞`, which is the repulsive half of
Proposition 4.25 (`M:O:prop:log-prep`, source lines 5588-5610) and closes
`HRS.log_prep_repulsive` (`HRS/Equilibrium/Preparation.lean`):

  `exact Repulsive.log_prep_repulsive_aux hd ρ hρ Λ hΛ B₀`

(`modNormalizerE` and `PreparationAux.KE` are definitionally equal).  The proof feeds
`exists_masterData` and `masterCutoffSize_le` to the generic
`DGRHS.Concentration.master_uniform_sublinear_exponential_envelope` (with `I = Unit`, `p = 2/3`)
for `β = max B₀ 0`, then reduces `0 ≤ γ ≤ β` to `β` by `KE_le_one_add`.

`sorry`-ed specifications; see `docs/REPULSIVE_PLAN.md` (REP-07).
-/
import HRS.Equilibrium.RepulsiveMaster

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ}

/-- The torus has a countably generated Borel σ-algebra (needed by the master envelope);
found by instance search (`BorelSpace` + second countability). -/
theorem countablyGenerated_torus (d : ℕ) : MeasurableSpace.CountablyGenerated (Torus d) :=
  inferInstance

/-- Uniform exponential moment at fixed `β ≥ 0` (DGR Theorem 2.2(i) on the torus): there is `C`
with `∫ exp(-β N F_N) dμ^{⊗N} ≤ C` for all `N ≥ 1`, together with integrability. -/
theorem exponential_moment_uniform (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => Real.exp (exponent d β N (withDensityReal ρ) X))
        (Measure.pi fun _ : Fin N => withDensityReal ρ) ∧
      (∫ X, Real.exp (exponent d β N (withDensityReal ρ) X)
        ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ≤ C := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have : MeasurableSpace.CountablyGenerated (Torus d) := countablyGenerated_torus d
  obtain ⟨δ, u₀, A, hδ, hδ2, hu₀, hA, hdata⟩ :=
    exists_masterData (μ := withDensityReal ρ) hd rfl hρ hΛ hβ
  choose D hD using hdata
  obtain ⟨K, hK⟩ := masterCutoffSize_le (μ := withDensityReal ρ) hd hβ hδ (by linarith) hA hu₀
  have hSize : ∀ (_θ : Unit) (n : ℕ) (hn : 1 ≤ n),
      DGRHS.Concentration.masterCutoffSize (withDensityReal ρ) (D n hn).kernel (D n hn).cap u₀
        ≤ 0 + K * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    intro _θ n hn
    rw [(hD n hn).1, (hD n hn).2, zero_add]
    exact (hK n hn).2
  obtain ⟨M, hM⟩ := DGRHS.Concentration.master_uniform_sublinear_exponential_envelope
    (I := Unit) (Ω := Torus d) (withDensityReal ρ)
    (fun _ n => exponent d β n (withDensityReal ρ))
    (fun _ n _ => (measurable_exponent hd β n (withDensityReal ρ)).aemeasurable)
    u₀ hu₀ (fun _ n hn => D n hn) 0 K ((2 : ℝ) / 3) (by norm_num) hSize
  exact ⟨M, fun N hN => hM () N hN⟩

/-- The repulsive half of Proposition 4.25: `sup_{N ≥ 2, γ ∈ [0, B₀]} K_{N,γ}(μ) < ∞`. -/
theorem log_prep_repulsive_aux (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (B₀ : ℝ) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (0 : ℝ) B₀,
      PreparationAux.KE (periodicRiesz d 0) N γ (withDensityReal ρ) ≤ ENNReal.ofReal C := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨C, hC⟩ := exponential_moment_uniform hd ρ hρ Λ hΛ (β := max B₀ 0) (le_max_right B₀ 0)
  refine ⟨1 + |C|, fun N hN γ hγ => ?_⟩
  obtain ⟨hint, hle⟩ := hC N (by omega)
  have h1 := KE_le_one_add (periodicRiesz d 0) N hγ.1 (hγ.2.trans (le_max_left B₀ 0))
    (withDensityReal ρ)
  rw [KE_eq_ofReal_integral (max B₀ 0) N (withDensityReal ρ) hint] at h1
  refine le_trans h1 ?_
  calc 1 + ENNReal.ofReal (∫ X, Real.exp (exponent d (max B₀ 0) N (withDensityReal ρ) X)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ))
      ≤ 1 + ENNReal.ofReal |C| :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hle.trans (le_abs_self C)))
    _ = ENNReal.ofReal (1 + |C|) := by
        rw [ENNReal.ofReal_add zero_le_one (abs_nonneg C), ENNReal.ofReal_one]

end Repulsive

end HRS

end
