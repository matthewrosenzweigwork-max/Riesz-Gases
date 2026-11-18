import HRS.Equilibrium.NormalFormProof
import HRS.Stochastic.SelectedFlow

/-!
# 4.16-DOM: the generator-domain clause of Proposition 4.16 (`normal_form`) (SPEC ONLY)

TeX M L4933: "The identity holds in the generator domain of the stationary realization, as well as pointwise off
collisions."  Proof: TeX M L4970 (cut off all pair separations below `ε`, Gibbs suppression `e^{-cβ/(N r^s)}` beats the
power growth of `F̂`, `∇F̂`, `∇²F̂` and of the cut-off derivatives; sequential cut-offs; dominated convergence).

Plan, truth analysis and line estimates: `HRS/MD/DOMPlan.md`.  Namespace `HRS.MD.DOM`.  Sorried statements live only in
this file.  The pointwise (off-collision) identity is the proved clause of `normal_form_proof`.

## What is encoded

The *closed generator domain* of the gradient particle dynamics on `L²(ℙ_{N,β})` is the graph-norm closure of
`(𝓛, C_c^∞(Ω_N \ collisions))` (`𝓛 = particleGen`).  `IsInClosedGenerator μ F G` says: there are smooth functions `Fn`
on the covering space, each vanishing outside a compact subset of the collision complement, with `Fn → F` and
`𝓛 Fn → G` in `L²(μ)` (and `∇Fn → ∇F` in `L²(μ)`; implied by the first two by symmetry of `𝓛`, kept so that
`configGrad F` is the gradient used downstream by the Lyons-Zheng formula).  Then `G` is the value of the closed
operator `𝓛̄` at `F`.  Because the generator of the stationary Markov semigroup of the strong solution extends `𝓛` on
such `Fn` (Itô/Dynkin for compactly supported smooth functions, which is `IsFKETest`) and is closed, this membership
implies membership in the generator domain of the stationary realisation with generator value `G` (Markov uniqueness is
not needed for this direction); that last step belongs to the Lyons-Zheng / 4.17 consumers, not to this statement.
No flow appears in the statements below.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS

namespace MD

namespace DOM

variable {d : ℕ}

/-- `G = 𝓛̄ F` for the closure `𝓛̄` of `𝓛 = particleGen` on `C_c^∞(Ω_N \ collisions)` in `L²(μ)` (graph norm, plus the
gradient seminorm).  Approximants are smooth on the covering space and supported in a compact set disjoint from the
collision set. -/
def IsInClosedGenerator (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) {N : ℕ} (μ : Measure (Config d N))
    (F G : Config d N → ℝ) : Prop :=
  ∃ Fn : ℕ → Config d N → ℝ,
    (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Fn n) 0) ∧
      ∃ K : Set (Config d N), IsCompact K ∧ Disjoint K (collisionSet d N) ∧ ∀ X, X ∉ K → Fn n X = 0) ∧
    Tendsto (fun n => eLpNorm (fun X => Fn n X - F X) 2 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun X => particleGen d s V β (Fn n) X - G X) 2 μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫⁻ X, ∑ i, ‖configGrad (Fn n) X i - configGrad F X i‖ₑ ^ 2 ∂μ) atTop (𝓝 0)

/-- The definition is satisfiable (anti-vacuity of the predicate itself): `0 ∈ D(𝓛̄)` with `𝓛̄ 0 = 0`. -/
theorem isInClosedGenerator_zero {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {N : ℕ} (μ : Measure (Config d N)) :
    IsInClosedGenerator d s V β μ (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun _ _ => 0, fun n => ⟨?_, ∅, isCompact_empty, Set.empty_disjoint _, fun _ _ => rfl⟩, ?_, ?_, ?_⟩
  · exact contDiff_const
  · simpa using tendsto_const_nhds
  · have h : ∀ X, particleGen d s V β (fun _ : Config d N => (0 : ℝ)) X = 0 := by
      intro X
      simp [particleGen, configLap, configGrad]
    simpa [h] using tendsto_const_nhds
  · have h : ∀ X i, configGrad (fun _ : Config d N => (0 : ℝ)) X i = 0 := by
      intro X i
      simp [configGrad]
    simpa [h] using tendsto_const_nhds

/-- `𝓛̄ F = G` and `G = G'` `μ`-a.e. give `𝓛̄ F = G'`. -/
theorem IsInClosedGenerator.congr_ae {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {N : ℕ} {μ : Measure (Config d N)}
    {F G G' : Config d N → ℝ} (h : IsInClosedGenerator d s V β μ F G) (hGG' : G =ᵐ[μ] G') :
    IsInClosedGenerator d s V β μ F G' := by
  obtain ⟨Fn, hFn, h1, h2, h3⟩ := h
  refine ⟨Fn, hFn, h1, ?_, h3⟩
  refine h2.congr' (Eventually.of_forall fun n => eLpNorm_congr_ae ?_)
  filter_upwards [hGG'] with X hX
  simp [hX]

/-- **4.16-DOM (`normal_form_domain`).**  Under the hypotheses of `normal_form` (`d ≥ 2`, `s = d/2`, `β > 0`, `V`
smooth, `ρ` the smooth positive thermal density), for every smooth test `f`, every pair corrector `ψ` for `f` and every
`N ≥ 2`, the centred pair statistic `F̂_N(ψ) = F_N(ψ) - E F_N(ψ)` belongs to the closed generator domain on
`L²(ℙ_{N,β})`, and `𝓛̄ F̂_N(ψ)` is the pointwise generator `𝓛 F_N(ψ)` (a function in `L²(ℙ_{N,β})`).
Route: `HRS/MD/DOMPlan.md` (cut-off by `∏_{i<j} θ(s(x_i - x_j)/ε)`, growth envelope of `F, ∇F, ∇²F, 𝓛F` by powers of
`w`, Gibbs density times powers of `w` bounded, dominated convergence). -/
theorem normal_form_domain {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ → ∀ N : ℕ, 2 ≤ N →
        IsInClosedGenerator d s V β (canonicalGibbs (periodicRiesz d s) V N β)
          (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (Fstat ψ))
          (particleGen d s V β (Fstat (N := N) ψ)) := by
  sorry

/-- **4.16 with the domain clause, in the form quoted at TeX L4933.**  Same hypotheses; the proved identity of
`normal_form_proof` (off collisions, hence `ℙ_{N,β}`-a.e.) turns `𝓛̄ F̂_N(ψ)` into the explicit expression obtained by
solving `𝓡_N(f) = -𝓛̄ F̂ + Ê - (2/N) ζ_N(a_f)` for `𝓛̄ F̂`, i.e.
`𝓛̄ F̂ = -𝓡_N(f) + Ê - (2/N) ζ_N(a_f)`.  Consequence of `normal_form_domain` and `normal_form_proof`; proved here. -/
theorem normal_form_domain_identity {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ → ∀ N : ℕ, 2 ≤ N →
        IsInClosedGenerator d s V β (canonicalGibbs (periodicRiesz d s) V N β)
          (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (Fstat ψ))
          (fun X =>
            -(Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                (quadStat (hTransport d s f) (withDensityReal ρ)) X) +
              centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ (N := N) ψ) X -
              (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X)) := by
  intro f K₁ ψ hf hψ N hN
  obtain ⟨C, hC⟩ := normal_form_proof hd hcrit β hβ V hV ρ hρ hρs
  have hid := (hC f K₁ ψ hf hψ N hN).2.2.2.1
  refine (normal_form_domain hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN).congr_ae ?_
  have hac : canonicalGibbs (periodicRiesz d s) V N β ≪ (volume : Measure (Config d N)) :=
    Q84d.q84d_gibbs_ac
  filter_upwards [hac.ae_le (Q84d.q84d_ae_not_collision (d := d) (N := N) (by omega))] with X hX
  have := hid X hX
  linarith

end DOM

end MD

end HRS

end
