import HRS.Whole.HeadlineStatement
import HRS.Whole.Bias

/-!
# Shifted field paths and critical stationary fluctuations (spec packet SPEC-W3):
Sections S7.9, S8.1, S8.2

Source: HRS whole-space supplement (S).

* S7.9 `S:cor:shifted-field-path` (S lines 6133-6169): the exactly centered field and path
  theorems with the leading deterministic shift `N^{3/2-p} b_{β,μ}`; setting of S lines 6073-6132
  (`B_m = E_m'`, `S:eq:field-embedding`, `S:eq:Gaussian-covariance`, `S:eq:stationary-SDE`).
* S8.1 `S:prop:critical-whole` (S lines 6212-6250): critical (`s = d/2`) static marginal
  expansion with the coefficient `β²|S^{d-1}|/d`, and the stationary path rates.
* S8.2 `S:prop:weighted-critical-forcing` (S lines 6308-6321): the weighted centered forcing
  estimate in the stationary quadratic model.  The nonlinear forcing `𝓡_N` is
  `(√N/2){D_μ(h_f) - E D_μ(h_f)}` (`M:Q:eq:normal-form`, M line 4915).
(S8.3-S8.8 are in `HRS/Whole/CriticalNoise.lean`.)

## Representation decisions

* The stationary quadratic model is `quadraticGradientDyn d s a β` (Headline.lean) started from the
  canonical law `canonicalGibbs` (`IsCanonicalRealization`: a strong solution on all of `[0,∞)`,
  independent Brownian motion, `S:eq:stationary-SDE`, S lines 6121-6126; and the invariance of
  `canonicalGibbs` for the dynamics, `GibbsInvariant`).  Every statement is "for
  every such realization".  `μ_β = ρ_β dx` is any `IsThermalEquilibrium d s a β ρ_β` (S3.4).
* The stationary Gaussian field `Z` (`S:eq:Gaussian-covariance`) is a process satisfying
  `IsLinearGaussianEvolutionW` along the constant reference `ρ_β`, noise level `q = β⁻¹`, initial
  covariance `susceptibilityCov` (`IsStationaryGaussianField`), for every horizon.
* The bias `b_{β,μ}` is an element of `B_m` through `OscDual.ofFun` applied to the density of `b`
  with respect to Lebesgue measure (`bias density × ρ`); the embedding `u ↦ uμ` of
  `S:eq:field-embedding` (S lines 6081-6087).  The constant path `𝐛(t) = b` is `constPath`.
* `r_N = (log N)/√N`; "`W_p/r_N → ‖𝐛‖`" (S8.1) is stated through `ℝ≥0∞`-valued `wassersteinE`
  with explicit two-sided `ofReal` bounds (no real-valued junk when infinite).
* The adjoint propagator `U_{t-r}` is `propagatorW C r t` (classical adjoint solution of the
  unprojected generator).  It differs from the semigroup of the projected generator `𝒜 = P_μ ℒ` by an
  additive constant, which every pairing with a zero-mass field (`μ_N - m_N`, `μ_N - μ`) ignores
  (S line 6552).  Its existence is part of the conclusion of the statements that use it.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff BoundedContinuousFunction

namespace HRS.Whole

variable {d : ℕ}

/-! ### The stationary quadratic model -/

/-- The data of a stationary realization of the canonical quadratic model (S lines 6121-6126,
`S:eq:canonical-law`, `S:eq:stationary-SDE`): independent vector Brownian motion `W`, initial law
`P_{N,β}` (`canonicalGibbs`), and a collision-free strong solution of the gradient dynamics with
`V = a|x|²/2` and `ν = β⁻¹` on every horizon.
Statement repair `Supplement repair P7` (docs/ISSUES.md): the solution is moreover filtered (`filtered`: some filtration
makes `W` Brownian and `X` adapted and progressive; the completed filtration of `(X₀, W)` is one).
Statement change M1b (2026-10-22): the realization carries the invariance of the canonical Gibbs law for this dynamics at this `N` (`invariant : GibbsInvariant d s a β N`; S L7901 "the canonical law
is invariant"), which is what makes the stationary claims (`law (X t) = canonicalGibbs`) available; it is a true property of the dynamics (it does not constrain `P, X₀, W, X`), to be removed
if the invariance is proved. -/
structure IsCanonicalRealization (d : ℕ) (s a β : ℝ) (N : ℕ) {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) : Prop where
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ζ t => W t ζ) P
  init : law P X₀ = canonicalGibbs (rieszKernel d s) (confinement a) N β
  solution : ∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X
  filtered : ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
    IsWholeFilteredSolution P ℱ W' W X
  invariant : GibbsInvariant d s a β N

/-- The stationary Gaussian linearized field `Z_β` (`S:eq:Gaussian-covariance`): a linear
Gaussian evolution on every horizon along the constant reference `ρ_β`, noise level `q = β⁻¹`, with
initial covariance the susceptibility form `⟨P_μφ, R_{β,μ}P_μψ⟩_{L²(μ)}`. -/
def IsStationaryGaussianField (d : ℕ) (s a β : ℝ) (m : ℝ) (ρβ : Euc d → ℝ) {Ω' : Type}
    [MeasurableSpace Ω'] (P' : Measure Ω') (Z : ℝ → Ω' → OscDual d m) : Prop :=
  ∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
    m β⁻¹ T' (susceptibilityCov (rieszKernel d s) (withDensityReal ρβ) β) Z

/-- The coefficients of the linear equation / the generator at the critical exponent `s = d/2` of
the quadratic model with thermal density `ρβ`. -/
def critCoeff (d : ℕ) (a β : ℝ) (ρβ : Euc d → ℝ) : WholeCoeff d :=
  (quadraticGradientDyn d ((d : ℝ) / 2) a β).coeff (fun _ => ρβ)

/-- The constant path `𝐛(t) = v`, `t ∈ [0,T]`, in `𝒳_T = C([0,T]; B_m)`. -/
def constPath (m T : ℝ) (v : OscDual d m) : OscPath d m T :=
  (ContinuousMap.const (Set.Icc (0 : ℝ) T) v : C(Set.Icc (0 : ℝ) T, OscDual d m))

/-- The bias `b_{β,μ} = 2A_{d,s}β^p (R_{β,μ}P_μρ) μ` as an element of `B_m`
(`S:eq:bias-measure`, `S:eq:field-embedding`): the embedding of the density `biasDensity · ρ`
with respect to Lebesgue measure. -/
def biasField (m : ℝ) (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) : OscDual d m :=
  OscDual.ofFun m fun x => biasDensity d s β ρ x * ρ x

/-- The density of the critical bias `b_{β,μ} = β²|S^{d-1}|/d (R_{β,μ}P_μρ) μ` relative to `μ`
(`S:eq:critical-whole-bias`, S lines 6220-6222), `s = d/2`. -/
def critBiasDensity (d : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ :=
  β ^ 2 * sphereArea d / d *
    responseInverse (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ x

/-- The critical bias as an element of `B_m` (as `biasField`). -/
def critBiasField (m : ℝ) (d : ℕ) (β : ℝ) (ρ : Euc d → ℝ) : OscDual d m :=
  OscDual.ofFun m fun x => critBiasDensity d β ρ x * ρ x

/-! ### S7.9 `S:cor:shifted-field-path` (S lines 6133-6169) -/

section Shifted

variable {s : ℝ}

/-- Corollary S7.9 (S:S:cor:shifted-field-path, TeX S L6133-6169) (S lines 6133-6169), static field
(`S:eq:shifted-static-rate`): `d/2 < s < d`, `p = d/s`, the exactly canonical quadratic trap
(`P_{N,β}`), `Y_N = √N(μ_N - μ)` (`etaB`, the mean-field centering `η_N`), `Z_0` a centered
Gaussian in `B_m` with covariance `⟨P_μφ, R_{β,μ}P_μψ⟩` (`IsCenteredGaussianOsc`), `m` in the
static range of S4.5 (`m > J + 2d`, `J > d/2 + 2` an integer):
`d_{C_b²(B_m)}(Law(Y_N), Law(Z_0 + N^{3/2-p} b_{β,μ})) ≤ C(√δ_N + N^{3/2-p-θ_{d,s}})`.
`C` depends on `d, s, a, β, J, m`.  Measurability of `Y_N` is part of the conclusion. -/
theorem shifted_field_static (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (J : ℕ) (hJ : (d : ℝ) / 2 + 2 < J) (m : ℝ)
    (hm : (J : ℝ) + 2 * d < m) :
    ∃ C : ℝ, ∀ N, 2 ≤ N → ∀ γ : Measure (OscDual d m),
      IsCenteredGaussianOsc m γ
        (susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β) →
      Measurable (fun X : EucConfig d N => etaB m X (thermalMeasure d s a β)) ∧
      smoothDist 2 (law (canonicalGibbs (rieszKernel d s) (confinement a) N β)
          (fun X : EucConfig d N => etaB m X (thermalMeasure d s a β)))
        (γ.map fun z => z + (N : ℝ) ^ (3 / 2 - biasP d s) •
          biasField m d s β (thermalDensity d s a β)) ≤
        C * (Real.sqrt (deltaN d s N) + (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) := by
  sorry

/-- Corollary S7.9 (S:S:cor:shifted-field-path, TeX S L6133-6169) (S lines 6133-6169), paths
(`S:eq:shifted-path-smooth`, `S:eq:shifted-path-W1`, S lines 6146-6156): `d/2 < s < d`,
`T < ∞`, `m = 24d + 240`, `Y_N^t = √N(μ_N^t - μ)`, `Z` the stationary Gaussian field, `𝐛` the
constant path `b_{β,μ}`, `w_N = (N^{-1/d} + √(C₀N^{s/d-1}))^{4/(d+4)}` (`localizationRate`) with
the heat-kernel completion constant `C₀` of S2.1(i) (`∃ C₀` with the completion property
`F_N(X_N, μ_β) + o_N ≥ 0` off collisions, chosen for the class, as in `whole_space_stationary`):
`d_{C_b²(𝒳_T)}(Law(Y_N), Law(Z + N^{3/2-p}𝐛)) ≤ C_T(√δ_N + w_N + N^{3/2-p-θ})` and
`W_1(Law(Y_N), Law(Z + N^{3/2-p}𝐛); 𝒳_T) ≤ C_T(δ_N^{3/20} + √w_N + N^{3/2-p-θ})`.
"The same bounds hold for a fixed-length stationary window with constants independent of its
starting time" (S line 6168): the window `a₀ ≥ 0` is quantified inside, `C_T` before it.
Technical hypotheses: `T > 0`, `N ≥ 2`.  Measurability of the path maps is part of the conclusion. -/
theorem shifted_field_path (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) :
    ∃ C₀ C : ℝ, (∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
        ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (withDensityReal ρβ) + oN d s C₀ N) ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d s a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
        IsStationaryGaussianField d s a β (wholeSpaceIndex d) ρβ P' Z →
      ∀ a₀ : ℝ, 0 ≤ a₀ →
        AEMeasurable (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X (fun _ => ρβ)) P ∧
        AEMeasurable (fun ζ' => processWindow (wholeSpaceIndex d) T a₀ Z ζ' +
          constPath (wholeSpaceIndex d) T ((N : ℝ) ^ (3 / 2 - biasP d s) •
            biasField (wholeSpaceIndex d) d s β ρβ)) P' ∧
        smoothDist 2 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (fun ζ' => processWindow (wholeSpaceIndex d) T a₀ Z ζ' +
              constPath (wholeSpaceIndex d) T ((N : ℝ) ^ (3 / 2 - biasP d s) •
                biasField (wholeSpaceIndex d) d s β ρβ))) ≤
          C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N +
            (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) ∧
        wassersteinE 1 (law P (flucPathW (wholeSpaceIndex d) T a₀ (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (fun ζ' => processWindow (wholeSpaceIndex d) T a₀ Z ζ' +
              constPath (wholeSpaceIndex d) T ((N : ℝ) ^ (3 / 2 - biasP d s) •
                biasField (wholeSpaceIndex d) d s β ρβ))) ≤
          ENNReal.ofReal (C * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N) +
            (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s))) := by
  sorry

/-- Corollary S7.9 (S:S:cor:shifted-field-path, TeX S L6133-6169) (S lines 6133-6169), critical path limit
`S:eq:critical-path-limit` (S lines 6157-6159, 6165-6167): at `s = 2d/3` (`p = 3/2`),
`√N(μ_N^· - μ_β) ⇒ Z + b_{β,μ_β}` in `C([0,T]; B_m)`, `m = 24d + 240`.  The particle systems form a
sequence `N ↦ (Ω_N, P_N, X_N)` of canonical realizations (`N ≥ 2`); weak convergence is
`∫ F(√N(μ_N^· - μ_β)) dP_N → ∫ F(Z + 𝐛) dP'` for every bounded continuous `F` on the path space. -/
theorem critical_path_limit (hd : 2 ≤ d) (hs : s = 2 * (d : ℝ) / 3) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) (T : ℝ) (hT : 0 < T) :
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
    ∀ {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
      [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → EucConfig d N)
      (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N),
      (∀ N : ℕ, 2 ≤ N → IsCanonicalRealization d s a β N (P N) (X₀ N) (W N) (X N)) →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
      IsStationaryGaussianField d s a β (wholeSpaceIndex d) ρβ P' Z →
      (∀ N : ℕ, 2 ≤ N → AEMeasurable (flucPathW (wholeSpaceIndex d) T 0 (Real.sqrt N) (X N)
        (fun _ => ρβ)) (P N)) ∧
      AEMeasurable (fun ζ' => processWindow (wholeSpaceIndex d) T 0 Z ζ' +
        constPath (wholeSpaceIndex d) T (biasField (wholeSpaceIndex d) d s β ρβ)) P' ∧
      ∀ F : OscPath d (wholeSpaceIndex d) T →ᵇ ℝ,
        Tendsto (fun N : ℕ => ∫ ζ, F (flucPathW (wholeSpaceIndex d) T 0 (Real.sqrt N) (X N)
            (fun _ => ρβ) ζ) ∂(P N)) atTop
          (𝓝 (∫ ζ', F (processWindow (wholeSpaceIndex d) T 0 Z ζ' +
            constPath (wholeSpaceIndex d) T (biasField (wholeSpaceIndex d) d s β ρβ)) ∂P')) := by
  sorry

end Shifted

/-! ### S8.1 `S:prop:critical-whole` (S lines 6212-6250) -/

section CriticalWhole

/-- Proposition S8.1 (S:S:prop:critical-whole, TeX S L6212-6250) (S lines 6212-6250), static part
(`S:eq:critical-whole-bias`): `d ≥ 2`, `s = d/2`, `μ = ρ dx` a bounded Lipschitz probability
density, `m_N` the first marginal of `Q_{N,β}(μ)`,
`‖dm_N/dμ - 1 - (log N/N) db_{β,μ}/dμ‖_{L²(μ)} ≤ C√(log N)/N`, `b_{β,μ} = β²|S^{d-1}|/d (R_{β,μ}P_μρ) μ`.
No positive lower bound, moment or compact support is assumed.  "Its constants for fixed `μ` are
uniform on compact positive inverse-temperature intervals": `C` depends on `ρ` and `[β₋,β₊]` and is
chosen before `β ∈ [β₋,β₊]` and `N`.  The law is asserted well defined and `R P ρ ∈ L²(μ)`.  The
pairing `b_{β,μ}(ρ) = ∫ ρ (db/dμ) dμ` is strictly positive for every `β > 0` (S lines 6234-6246).
Technical hypothesis: `N ≥ 2` (the right side vanishes at `N = 1`). -/
theorem critical_whole_marginal (hd : 2 ≤ d) (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ)
    (hbdd : ∃ M : ℝ, ∀ x, ρ x ≤ M) (hlip : ∃ Λ : ℝ≥0, LipschitzWith Λ ρ) (βm βp : ℝ)
    (hβm : 0 < βm) (hβ : βm ≤ βp) :
    (∀ β : ℝ, 0 < β → 0 < l2Inner (withDensityReal ρ) ρ (critBiasDensity d β ρ)) ∧
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ N : ℕ, 2 ≤ N →
      GibbsWellDefined (fun x y => rieszKernel d ((d : ℝ) / 2) (x - y)) N β (withDensityReal ρ) ∧
      MemLp (critBiasDensity d β ρ) 2 (withDensityReal ρ) ∧
      ∃ φ : Euc d → ℝ, Measurable φ ∧ (∀ x, 0 ≤ φ x) ∧
        firstMarginal (modulatedGibbs (rieszKernel d ((d : ℝ) / 2)) N β (withDensityReal ρ)) =
          (withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (φ x)) ∧
        MemLp (fun x => φ x - 1 - (Real.log N / N) * critBiasDensity d β ρ x) 2
          (withDensityReal ρ) ∧
        l2Norm (withDensityReal ρ) (fun x => φ x - 1 - (Real.log N / N) * critBiasDensity d β ρ x) ≤
          C * Real.sqrt (Real.log N) / N := by
  sorry

/-- Proposition S8.1 (S:S:prop:critical-whole, TeX S L6212-6250) (S lines 6212-6250), centered path
(`S:eq:critical-whole-W2`): `d ≥ 2`, `s = d/2`, `V = a|x|²/2` (`a, β > 0`), `μ = μ_β`,
`m ≥ 24d + 240`, `𝒳 = C([0,T]; B_m)`: for the stationary canonical diffusion (any
`IsCanonicalRealization`) and its stationary Gaussian field `Z_β`,
`sup_{u≥0} W_2^𝒳(Law[ζ_N^{u+·}], Law[Z_β]) ≤ C_T N^{-1/2}`, `ζ_N^t = √N(μ_N^t - m_N^t)`.  `C_T`
depends on `d, a, β, T, m` and is chosen before the realization.  Measurability of the window
paths is part of the conclusion.  Technical hypotheses: `T > 0` (`T < ∞`), `N ≥ 2`. -/
theorem critical_whole_W2 (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
        AEMeasurable (processWindow m T 0 Z) P' ∧
        ∀ u : ℝ, 0 ≤ u →
          AEMeasurable (zetaPathW m T u P X) P ∧
          wassersteinE 2 (law P (zetaPathW m T u P X)) (law P' (processWindow m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  sorry

/-- Proposition S8.1 (S:S:prop:critical-whole, TeX S L6212-6250) (S lines 6212-6250), mean-field-centered constants
(`S:eq:critical-whole-constants`): with `r_N = (log N)/√N` and `𝐛(t) = b_{β,μ}` on `[0,T]`, for
`1 ≤ p ≤ 2`, `r_N^{-1} W_p^𝒳(Law[η_N^{u+·}], Law[Z_β]) → ‖𝐛‖_𝒳 = ‖b_{β,μ}‖_{B_m}` uniformly in
`u ≥ 0`, `η_N^t = √N(μ_N^t - μ)`.  Stated as: for every `ε > 0` there is `N₀` such that for all
`N ≥ N₀`, all realizations and all `u ≥ 0`,
`r_N(‖𝐛‖ - ε) ≤ W_p ≤ r_N(‖𝐛‖ + ε)` (in `ℝ≥0∞`). -/
theorem critical_whole_constants (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
        AEMeasurable (processWindow m T 0 Z) P' ∧
        ∀ u : ℝ, 0 ≤ u →
          AEMeasurable (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)) P ∧
          ENNReal.ofReal (Real.log N / Real.sqrt N *
              (‖constPath m T (critBiasField m d β ρβ)‖ - ε)) ≤
            wassersteinE p (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (processWindow m T 0 Z)) ∧
          wassersteinE p (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (processWindow m T 0 Z)) ≤
            ENNReal.ofReal (Real.log N / Real.sqrt N *
              (‖constPath m T (critBiasField m d β ρβ)‖ + ε)) := by
  sorry

/-- Proposition S8.1 (S:S:prop:critical-whole, TeX S L6212-6250) (S lines 6212-6250), smooth metrics (last sentence,
S lines 6247-6249): in the sum-norm `C_b^k` metric, `k ≥ 2`, the limit of
`r_N^{-1} d_k^𝒳(Law[η_N^{u+·}], Law[Z_β])` is `sup_{‖F‖_{C_b^k} ≤ 1} |E[DF(Z_β)[𝐛]]|`
(`smoothConstant`: the sup over the unit ball, which is symmetric), uniformly in `u ≥ 0`. -/
theorem critical_whole_smooth (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) (k : ℕ) (hk : 2 ≤ k) :
    ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ →
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
        AEMeasurable (processWindow m T 0 Z) P' ∧
        ∀ u : ℝ, 0 ≤ u →
          AEMeasurable (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)) P ∧
          |(Real.log N / Real.sqrt N)⁻¹ *
              smoothDist k (law P (flucPathW m T u (Real.sqrt N) X (fun _ => ρβ)))
                (law P' (processWindow m T 0 Z)) -
            smoothConstant P' k (processWindow m T 0 Z)
              (constPath m T (critBiasField m d β ρβ))| ≤ ε := by
  sorry

end CriticalWhole

/-! ### S8.2 `S:prop:weighted-critical-forcing` (S lines 6308-6321) -/

section Forcing

/-- Proposition S8.2 (S:S:prop:weighted-critical-forcing, TeX S L6308-6321) (S lines 6308-6321): in the stationary
quadratic model of S8.1 (`d ≥ 2`, `s = d/2`, `V = a|x|²/2`, `μ = μ_β`, canonical stationary
particles, `m ≥ 24d + 240`, `φ_j = λ_j^{-m/2}h_j` is `oscTestFun m`), the centered nonlinear
forcing `𝓡_N(f) = (√N/2){D_μ(h_f) - E D_μ(h_f)}` (`M:Q:eq:normal-form`, M line 4915;
`D_μ(h_f)(X) = commForcing`: `h_f = (∇f(x) - ∇f(y))·∇g(x-y)`, deleted diagonal, no factor `1/2`,
the expectation under the stationary law) satisfies
`sup_{a₀ ≥ 0} (E[sup_{0≤t≤T} ∑_j |∫_0^{a₀+t} 𝓡_N(U_{a₀+t-r}φ_j)(X_N^r) dr|²])^{1/2} ≤ C_T N^{-1/2}`.
(`a₀` is the window start called `a` in the source, which also calls the confinement `a`.)  `U_{t-r}`
is the classical adjoint evolution (`propagatorW`); its existence for every `φ_j` and terminal time
and the almost sure integrability of the `r`-integrands, the `P`-integrability of `commForcing` at each `r` and the integrability of `r ↦ E[commForcing]` on `[0,t]` (so the centering `E D_μ(h_f)` is not a junk `0`) are part of the conclusion (so that
`propagatorW`, the Bochner integrals are not junk).  `C_T` depends on `d, a, β, T, m` and is
chosen before the realization.  Technical hypotheses: `T > 0`, `N ≥ 2`. -/
theorem weighted_critical_forcing (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      (∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
        ∃ f, IsClassicalAdjointW (critCoeff d a β ρβ) t (oscTestFun m α) f) ∧
      (∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
        IntegrableOn (fun r => commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
          (withDensityReal ρβ) X α t r ζ) (Set.Icc 0 t)) ∧
      (∀ α : MultiIndex d, ∀ t : ℝ, 0 ≤ t →
        (∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (fun ζ => commForcing (critCoeff d a β ρβ)
          ((d : ℝ) / 2) m (withDensityReal ρβ) X α t r ζ) P) ∧
        IntegrableOn (fun r => ∫ ζ, commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
          (withDensityReal ρβ) X α t r ζ ∂P) (Set.Icc 0 t)) ∧
      ∀ a₀ : ℝ, 0 ≤ a₀ →
        (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
            ∫ r in Set.Icc (0 : ℝ) (a₀ + t),
              (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
                  (withDensityReal ρβ) X α (a₀ + t) r ζ -
                ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m (withDensityReal ρβ) X α
                  (a₀ + t) r ζ' ∂P))) ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  sorry

end Forcing

end HRS.Whole
