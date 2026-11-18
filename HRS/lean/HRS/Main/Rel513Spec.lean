import HRS.Sections.Sec5
import HRS.Equilibrium.QuadraticVariance
import HRS.Equilibrium.ResponseVariance
import HRS.Equilibrium.MarginalDensity
import HRS.Energy.Commutator.AbsConv

/-!
# HRS.Main.Rel513Spec -- Proposition 5.13, last sentence (statements only)

The last sentence of Proposition 5.13 (`M:O:prop:relative`, TeX 7159-7171) says that the abstract
statement `relative_remainder` (Sec5.lean) applies to the stationary Riesz remainder
`R_{N,stat}(φ)` (`P:eq:stationary-R`, TeX 4009-4047), throughout `0 ≤ s < d`, "with the actual
finite-particle center and the complete marginal-induced linear term retained".  Its content is
the `L²(P_{N,β})` bound `P:eq:stationary-R-test` (this file, part (a)) fed into `relative_remainder`
with `a ≡ 1` (part (b)).

All theorems here are `sorry`'d statements (spec only, no proofs).

* `stationaryRemainder` is `R_{N,stat}(φ)` evaluated at `X ∈ 𝕋^{dN}`:
  `√N ((μ_N - m_N)(H_{μ,φ} - H_{m_N,φ})) - √N (F_N^{h_φ}(X; m_N) - E_{P_{N,β}} F_N^{h_φ}(·; m_N))`
  with `h_φ = h_{∇φ}`, `h_φ(x,y) = (∇φ(x) - ∇φ(y))·∇g(x - y)` (`commKernel (periodicRieszGrad d s)
  (Torus.grad φ)`, `0` on the diagonal), `H_{ν,φ}(x) = ∫ h_φ(x,y) dν(y)` (`Hc`), `μ = ρ_β dx`
  (`withDensityReal ρβ`), `m_N` the first marginal of `P_{N,β}` (the *actual* finite-particle center),
  and `D_N(h;m_N) = 2 F_N^h` (`quadStat h ν = 2 * modulatedEnergy h . ν`, checked in the proof).
  The marginal-induced linear term `ζ_N(H_μ - H_{m_N})` is kept, with `ζ_N = √N(μ_N - m_N)`.
* Hypotheses: `d ≥ 2` as in the TeX standing assumption; `0 ≤ s < d`; `β > 0`; `V` smooth;
  `ρβ` a smooth strictly positive thermal density (`SmoothPosDensity ρβ`, `IsThermalDensity`).
  `φ` is required **smooth** (`Torus.IsSmooth`), stronger than the TeX `C²`; this makes
  `Torus.grad φ` Lipschitz and `cbNorm 2 φ` finite, so `quadStat_variance` applies with
  `B = C ‖φ‖_{C²}` and the constant is uniform in `φ`.
* Only the test-function bound `P:eq:stationary-R-test` is covered (with `ε_N = √δ_N`, the TeX
  convention of line 3344).  NOT covered: the field-level bound `P:eq:stationary-R-field`
  (sup over `t` in `L²(E_M)`), the Minkowski time-integrated bound in `E_M`, and the Itô identity
  `P:eq:stationary-identity` itself.
* `P_{N,β}` is a probability measure (`canonicalGibbs_isProbability`, needs `0 < canonicalPartition`,
  here from `canonicalPartition_pos_riesz`); it is not a hypothesis of the theorems.
* The Markov family in part (b) is a hypothesis exactly as in `relative_remainder`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Main

variable {d : ℕ}

/-- `P_{N,β}` is a probability measure as soon as its (Bochner) partition function is positive
(positivity forces integrability of the Boltzmann weight, so the `withDensity` is finite and
the `lintegral` normaliser is `ofReal` of the Bochner one). -/
theorem canonicalGibbs_isProbability (g V : Torus d → ℝ) (N : ℕ) (β : ℝ)
    (hZ : 0 < canonicalPartition g V N β) :
    IsProbabilityMeasure (canonicalGibbs g V N β) := by
  sorry

/-- The partition function of the Riesz canonical Gibbs ensemble is positive (`β > 0`, `V` smooth,
`0 ≤ s < d`, `N ≥ 1`): the Hamiltonian is bounded below (periodic Riesz/log kernel bounded below,
`V` continuous) and measurable. -/
theorem canonicalPartition_pos_riesz (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {N : ℕ} (hN : 1 ≤ N) :
    0 < canonicalPartition (periodicRiesz d s) V N β := by
  sorry

/-- The stationary Riesz remainder `R_{N,stat}(φ)` of `P:eq:stationary-R` (TeX 4009-4047) as a
function of the configuration `X`, with `h = h_{∇φ}`, `μ = ρβ dx`, `Π = P_{N,β}`,
`m = m_N = Π^{(1)}`:
`√N ((∫ (H_μ - H_m) d μ_N(X)) - ∫ (H_μ - H_m) dm) - √N (F^h(X; m) - ∫ F^h(X'; m) dΠ(X'))`. -/
def stationaryRemainder (d : ℕ) (s β : ℝ) (V ρβ : Torus d → ℝ) (N : ℕ) (φ : Torus d → ℝ)
    (X : Config d N) : ℝ :=
  Real.sqrt N *
      ((∫ y, (Quad.Hc (commKernel (periodicRieszGrad d s) (Torus.grad φ)) (withDensityReal ρβ) y
              - Quad.Hc (commKernel (periodicRieszGrad d s) (Torus.grad φ))
                  (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) y) ∂(empirical X))
        - ∫ y, (Quad.Hc (commKernel (periodicRieszGrad d s) (Torus.grad φ)) (withDensityReal ρβ) y
              - Quad.Hc (commKernel (periodicRieszGrad d s) (Torus.grad φ))
                  (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) y)
            ∂(firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)))
    - Real.sqrt N *
      (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X
          (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))
        - ∫ X', modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X'
              (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))
            ∂(canonicalGibbs (periodicRiesz d s) V N β))

/-- Measurability of `X ↦ R_{N,stat}(φ)(X)` (needed because `eLpNorm` and the hypothesis `hA`
of `relative_remainder` use a lower integral / joint measurability, and the Bochner integrals
over `Π` and `m` inside are constants in `X`). -/
theorem stationaryRemainder_measurable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρβ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (N : ℕ) (hN : 2 ≤ N) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    Measurable (stationaryRemainder d s β V ρβ N φ) := by
  sorry

/-- Part (a) of the last sentence of Proposition 5.13: `P:eq:stationary-R-test` with
`ε_N = √δ_N`,
`‖R_{N,stat}(φ)‖_{L²(P_{N,β})} ≤ C √δ_N ‖φ‖_{C²}`, for `N ≥ 2`, smooth `φ`, throughout
`0 ≤ s < d` (`d ≥ 2`), with `C` independent of `N` and `φ`. -/
theorem stationary_remainder_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρβ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      eLpNorm (stationaryRemainder d s β V ρβ N φ) 2 (canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * Real.sqrt (deltaN d s N) * Torus.cbNorm 2 φ) := by
  sorry

/-- Part (b) of the last sentence of Proposition 5.13: given `‖R_{N,stat}(φ)‖_{L²(P_{N,β})} ≤ ε`
(e.g. `ε = C √δ_N ‖φ‖_{C²}` from `stationary_remainder_L2`), `relative_remainder` applies with
`A^r ≡ R_{N,stat}(φ)`, `a ≡ 1`, `∫_0^t a = t`: for any Markov family `κ` with invariant law
`P_{N,β}`, any process `Xp` with one-time laws `ν κ_r`, `ν ≪ P_{N,β}`, `‖dν/dP_{N,β}‖_{L²} ≤ R`,
`E |∫_0^t (R(Xp^r) - E R(Xp^r)) dr| ≤ 2 R t ε`.  The binders are exactly those of
`relative_remainder` (with `S = Config d N`, `Pi = canonicalGibbs (periodicRiesz d s) V N β`). -/
theorem stationary_remainder_time_integral (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρβ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (N : ℕ) (hN : 2 ≤ N) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : eLpNorm (stationaryRemainder d s β V ρβ N φ) 2
      (canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal ε)
    (κ : ℝ → ProbabilityTheory.Kernel (Config d N) (Config d N))
    [∀ r, ProbabilityTheory.IsMarkovKernel (κ r)]
    (hinv : ∀ r, 0 ≤ r →
      (canonicalGibbs (periodicRiesz d s) V N β).bind (κ r) = canonicalGibbs (periodicRiesz d s) V N β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xp : ℝ → Ω → Config d N) (hXp : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (ν : Measure (Config d N)) (hν : ν ≪ canonicalGibbs (periodicRiesz d s) V N β) (R : ℝ)
    (hR : eLpNorm (ν.rnDeriv (canonicalGibbs (periodicRiesz d s) V N β)) 2
      (canonicalGibbs (periodicRiesz d s) V N β) ≤ ENNReal.ofReal R)
    (hlaw : ∀ r, 0 ≤ r → P.map (Xp r) = ν.bind (κ r)) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal |∫ r in (0 : ℝ)..t,
        (stationaryRemainder d s β V ρβ N φ (Xp r ω)
          - ∫ ω', stationaryRemainder d s β V ρβ N φ (Xp r ω') ∂P)| ∂P ≤
      ENNReal.ofReal (2 * R * t * ε) := by
  sorry

end HRS.Main

end
