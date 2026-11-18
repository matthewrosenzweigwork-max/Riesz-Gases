import HRS.Main.Assumptions
import HRS.Dynamics.InitialData
import HRS.Main.A33Aux18

/-!
# The linear approximation and the limiting field (main manuscript, Appendix A)

Specification file SPEC-A.  Sources (`HRS_periodic_main_20261008T010000Z.tex`):
* the prose `B:sec:main-surrogate` (L10260-10292): the linear approximation
  `𝔖_N^t[φ⃗] = (A_N ⟨U_N^{0,t}φ_a, η°⟩ + G_a)_a` (`B:eq:surrogate-def`), the Gaussian covariance
  `𝗏_N^t[φ_a,φ_b]` (`B:eq:surrogate-cov`), the field `η_{N,lin}^t = A_N V_N^{t,0} η° + G_N^t`
  (`B:eq:surrogate-field-torus`), and the `N`-independent limit field obtained by replacing the
  coefficient quadruple `(β_N, μ_{β_N}, A_N, 2σ_N²/(Nβ_N))` by `(β_∞, μ_{β_∞}, A, 2/β_*)`;
* Proposition A.33 `prop:periodic-limit-field` (L11310-11318).

## Representation decisions

* The *laws* of the linear approximations are given as explicit measures: the law of
  `A_N ⟨U φ, η°⟩ + G` with `G` Gaussian independent of `η°` is the additive convolution
  (`Measure.conv`) of the law of `A_N ⟨U φ, η°⟩` with the centered Gaussian `N(0, 𝗏)`.  This makes the
  comparison statements independent of the existence of an independent `G` on the given probability
  space (the TeX "`G_N^t` is chosen independent of `𝓕_0^in`").
* The `H^{-γ}`-valued Gaussian field `G_N^t` is any law `νG` that is a centered Gaussian measure on
  `NegSobolev d γ` with covariance form `HRS.noiseCovariance` (`IsLinearFieldNoise`); it is unique
  (Gaussian laws on a separable Hilbert space are determined by their covariance on a dense class of
  tests), and its existence is Proposition A.33 (`periodic_limit_field`).  Statements are made for
  every such `νG`.
* The transported initial field `V_N^{t,0} η°` is `transportField`:
  `⟨e_k, V^{t,0} F⟩ := ⟨U^{0,t} e_k, F⟩` on the real trigonometric system `e_k = realMode k`
  (zero mode dropped, as for all of `NegSobolev`), with `U` the project's classical adjoint
  propagator `HRS.propagator`.
* Weak convergence of laws is `ConvergesInLaw` (the portmanteau form: convergence of the integrals of
  bounded continuous functions).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### Statistics and their laws (finite families of tests and times) -/

section Statistics

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The particle statistics `(⟨φ_a, σ Ξ_N^{t_a}⟩)_a`, `Ξ_N^t = μ_N^t - μ_{β_N}^t`
(`μ_N^t` the empirical measure of `X_N^t`, `μ_{β_N}^t = ρ t dx`), a vector in `ℝ^ι`. -/
def fluctStat (σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (ts : ι → ℝ)
    (φ : ι → Torus d → ℝ) (ω : Ω) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun a =>
    σ * (pair (empirical (X (Real.toNNReal (ts a)) ω)) (φ a) - pair (withDensityReal (ρ (ts a))) (φ a))

/-- The law of the particle statistics. -/
def fluctStatLaw (P : Measure Ω) (σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ)
    (ts : ι → ℝ) (φ : ι → Torus d → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  law P (fluctStat σ X ρ ts φ)

end Statistics

section Surrogate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The covariance matrix of the Gaussian blocks `(G_a)` of `B:eq:surrogate-def`
(`B:eq:surrogate-cov`, TeX L10272-10276, with the cross-covariance of the multi-time recipe of
`B:rem:multitime`): `2q ∫_0^{t_a ∧ t_b} ⟨∇U^{r,t_a}φ_a · ∇U^{r,t_b}φ_b, μ^r⟩ dr`,
`q = σ²/(Nβ)` (`2q = 2σ²/(Nβ)`); the same expression as in `HRS.IsLinearFluctuationSolution`. -/
def surrogateCov (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q : ℝ) (ts : ι → ℝ)
    (φ : ι → Torus d → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun a b =>
    2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
      inner ℝ (Torus.grad (propagator D ρ r (ts a) (φ a)) x)
        (Torus.grad (propagator D ρ r (ts b) (φ b)) x) * ρ r x

/-- The law of the linear approximation `𝔖_N^t[φ⃗] = (A ⟨U^{0,t_a}φ_a, η°⟩ + G_a)_a`
(`B:eq:surrogate-def`, TeX L10266-10270), `G` centered Gaussian with covariance `surrogateCov`
independent of `η°`: the convolution of the law of `(A η°(U^{0,t_a}φ_a))_a` under `P` with the
centered Gaussian of covariance `surrogateCov D ρ q`.  `η` is the random functional `η°`,
`D, ρ` the coefficients (`β_N, μ_{β_N}`), `A = A_N`, `q = q_N`. -/
def surrogateStatLaw {Ω : Type*} [MeasurableSpace Ω] (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (A q : ℝ) (ts : ι → ℝ) (φ : ι → Torus d → ℝ) (P : Measure Ω)
    (η : Ω → (Torus d → ℝ) → ℝ) : Measure (EuclideanSpace ℝ ι) :=
  law P (fun ω => (WithLp.toLp 2 fun a => A * η ω (propagator D ρ 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι)) ∗ multivariateGaussian 0 (surrogateCov D ρ q ts φ)

end Surrogate

/-! ### Fields -/

/-- The transported initial field `V^{t,0} F` (the transpose of the adjoint propagator `U^{0,t}`):
`⟨e_k, V^{t,0} F⟩ = ⟨U^{0,t} e_k, F⟩` for the real trigonometric system `e_k = realMode k`, as an
element of `E_γ = NegSobolev d γ`. -/
def transportField (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t γ : ℝ) (F : NegSobolev d γ) :
    NegSobolev d γ :=
  NegSobolev.ofSeq γ fun k => NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k))

/-- `νG` is the law of the Gaussian field `G^t` of the linear approximation at time `t`: a centered
Gaussian probability measure on `E_γ = H^{-γ}_0` with covariance
`2q ∫_0^t ⟨∇U^{r,t}φ·∇U^{r,t}ψ, μ^r⟩ dr` (`HRS.noiseCovariance`, `B:eq:surrogate-cov`),
`q = σ_N²/(Nβ_N)` (resp. `β_*⁻¹` for the limit). -/
def IsLinearFieldNoise (D : DynData d) (ρ : ℝ → Torus d → ℝ) (q t : ℝ) (γ : ℝ)
    (νG : Measure (NegSobolev d γ)) : Prop :=
  IsProbabilityMeasure νG ∧ IsCenteredGaussianWithCov γ νG (noiseCovariance D ρ q t)

/-- The law of the particle field `σ Ξ_N^t = σ(μ_N^t - μ_{β_N}^t)` in `E_γ`. -/
def particleFieldLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) (σ : ℝ) (γ : ℝ)
    (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (t : ℝ) : Measure (NegSobolev d γ) :=
  law P (fun ω => σ • NegSobolev.ofMeasureDiff γ (empirical (X (Real.toNNReal t) ω))
    (withDensityReal (ρ t)))

/-- The law of the linear approximation field `η_{N,lin}^t = A V^{t,0} η° + G^t`
(`B:eq:surrogate-field-torus`, TeX L10279): the convolution of the law of `A V^{t,0} η°`
(`η° = η` a `NegSobolev d γ`-valued random element on `(Ω, P)`) with the Gaussian law `νG` of `G^t`
(independent of `η°`). -/
def linearFieldLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) (A t : ℝ) (γ : ℝ) (η : Ω → NegSobolev d γ)
    (νG : Measure (NegSobolev d γ)) : Measure (NegSobolev d γ) :=
  haveI := InitialDataAux.negSobolev_secondCountable d γ
  law P (fun ω => A • transportField D ρ t γ (η ω)) ∗ νG

/-- The law of the `N`-independent limit field `η^t` (TeX L10285-10290): the coefficients are replaced
by `(β_∞, μ_{β_∞}, A, 2/β_*)` (`LimitCoeffs`), `η°` has the fixed law `νin` (`η° ∼ νin`, an
`N`-independent initial law), and `νGlim` is the Gaussian law of the limiting block (the cylindrical
Wiener process is independent of `η°`). -/
def limitFieldLaw (S : MainData d) (L : LimitCoeffs d) (γ : ℝ) (νin : Measure (NegSobolev d γ))
    (t : ℝ) (νGlim : Measure (NegSobolev d γ)) : Measure (NegSobolev d γ) :=
  linearFieldLaw νin (L.dyn S) L.ρ L.A t γ id νGlim

/-- Weak convergence of laws (portmanteau form): `∫ f dμ_N → ∫ f dν` for every bounded continuous
real `f`.  For random elements this is Mathlib's `TendstoInDistribution`. -/
def ConvergesInLaw {E : Type*} [TopologicalSpace E] [MeasurableSpace E] (μ : ℕ → Measure E)
    (ν : Measure E) : Prop :=
  ∀ f : E →ᵇ ℝ, Tendsto (fun N => ∫ x, f x ∂(μ N)) atTop (𝓝 (∫ x, f x ∂ν))

/-! ### Proposition A.33 -/

/-- A distribution-valued solution of the linearized equation `H:eq:linear-equation` in mild form,
*without* a path-continuity requirement: the same as `HRS.IsLinearFluctuationSolution` minus its
field `cont`.  Proposition A.33 (TeX L11310-11318) only asserts a "distribution-valued solution";
path continuity is claimed only for the continuous version in `H^{-(γ+2)}` (Proposition A.11,
L10386-10391, which uses `IsLinearFluctuationSolution`). -/
structure IsLinearFluctuationProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m q T : ℝ) (Y₀ : Ω → NegSobolev d m)
    (Y : ℝ → Ω → NegSobolev d m) : Prop where
  init : ∀ᵐ ω ∂P, Y 0 ω = Y₀ ω
  meas : ∀ t, Measurable (Y t)
  gaussian_part : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ),
    (∀ a, ts a ∈ Set.Icc 0 T) → (∀ a, Torus.IsSmooth (φ a)) →
    let G : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) - NegSobolev.eval (Y₀ ω) (propagator D ρ 0 (ts a) (φ a))
    ProbabilityTheory.IndepFun G Y₀ P ∧
    law P G = ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun a b =>
      2 * q * ∫ r in Set.Icc 0 (min (ts a) (ts b)), ∫ x,
        inner ℝ (Torus.grad (propagator D ρ r (ts a) (φ a)) x)
          (Torus.grad (propagator D ρ r (ts b) (φ b)) x) * ρ r x)

/-- Proposition A.33 `M:prop:periodic-limit-field` (TeX L11310-11318).  Under the hypotheses of the
periodic field comparison (the adjoint hypotheses of Proposition 3.9 at the level `γ = m_*+d+3`,
`AdjointData`, with regime `Rg`) and a noise level `q ≥ 0` (**technical**: `q = σ_N²/(Nβ_N) ≥ 0`
makes the covariance positive semidefinite):
(1) for every `t ∈ [0,T]` the covariance `B:eq:surrogate-cov` defines a centered Gaussian field in
`H^{-γ}(𝕋^d)` (`IsLinearFieldNoise`); the independence from the initial fluctuation field is part
of the solution concept (`gaussian_part`);
(2) for every initial law `ν₁` on `E_γ` there is a distribution-valued solution `Y` of the linearized
equation (`IsLinearFluctuationProcess`: initial field plus stochastic convolution, mild form) with
`Y⁰ ∼ ν₁`, and it is unique: any two such solutions have the same finite-dimensional laws on smooth
tests, `Law (Y_{t_a}(φ_a))_a` (the TeX asserts uniqueness among distribution-valued solutions, via the
adjoint identity and density of smooth tests, and no path continuity here).
The same statement applied to the limiting coefficients `(β_∞, μ_{β_∞}, β_*⁻¹)` gives the limiting
field (the proposition is stated for arbitrary admissible coefficients `(D, ρ, q)`). -/
theorem periodic_limit_field (hd : 1 ≤ d) (Rg : PDE.Regime) (ν₀ MB Λ VB : ℝ)
    (D : DynData d) (T : ℝ) (ρ : ℝ → Torus d → ℝ)
    (hA : PDE.AdjointData D.s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) (q : ℝ) (hq : 0 ≤ q) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∃ νG : Measure (NegSobolev d (gammaIdx d : ℝ)),
        IsLinearFieldNoise D ρ q t (gammaIdx d : ℝ) νG) ∧
    ∀ ν₁ : Measure (NegSobolev d (gammaIdx d : ℝ)), IsProbabilityMeasure ν₁ →
      (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
          (Y₀ : Ω' → NegSobolev d (gammaIdx d : ℝ)) (Y : ℝ → Ω' → NegSobolev d (gammaIdx d : ℝ)),
          Measurable Y₀ ∧ law P' Y₀ = ν₁ ∧
          IsLinearFluctuationProcess P' D ρ (gammaIdx d : ℝ) q T Y₀ Y) ∧
      ∀ (Ω₁ Ω₂ : Type) (_ : MeasurableSpace Ω₁) (_ : MeasurableSpace Ω₂)
          (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (_ : IsProbabilityMeasure P₁)
          (_ : IsProbabilityMeasure P₂)
          (Y₀₁ : Ω₁ → NegSobolev d (gammaIdx d : ℝ)) (Y₀₂ : Ω₂ → NegSobolev d (gammaIdx d : ℝ))
          (Y₁ : ℝ → Ω₁ → NegSobolev d (gammaIdx d : ℝ))
          (Y₂ : ℝ → Ω₂ → NegSobolev d (gammaIdx d : ℝ)),
        law P₁ Y₀₁ = ν₁ → law P₂ Y₀₂ = ν₁ →
        IsLinearFluctuationProcess P₁ D ρ (gammaIdx d : ℝ) q T Y₀₁ Y₁ →
        IsLinearFluctuationProcess P₂ D ρ (gammaIdx d : ℝ) q T Y₀₂ Y₂ →
        ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ),
          (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) → (∀ a, Torus.IsSmooth (φ a)) →
          law P₁ (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y₁ (ts a) ω) (φ a) :
              EuclideanSpace ℝ (Fin p))) =
            law P₂ (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y₂ (ts a) ω) (φ a) :
              EuclideanSpace ℝ (Fin p))) := by
  have hJ : PDE.mStar d ≤ gammaIdx d := by unfold gammaIdx; omega
  have hJ2 : PDE.mStar d + d ≤ gammaIdx d := by unfold gammaIdx; omega
  let S : HRS.A33.A33Setup d :=
    { J := gammaIdx d, hJ := hJ, hJ2 := hJ2, hd := hd, R := Rg, MB := MB, Λ := Λ, VB := VB,
      ν₀ := ν₀, D := D, T := T, ρ := ρ, hA := hA }
  obtain ⟨e⟩ := HRS.A33.a33_exists_equiv hd
  refine ⟨?_, fun ν₁ hν₁ => ?_⟩
  · intro t ht
    obtain ⟨νG, hp, hc, hcov⟩ := HRS.A33.a33_noise_exists S q hq ht
    refine ⟨νG, ?_⟩
    unfold IsLinearFieldNoise IsCenteredGaussianWithCov
    exact ⟨hp, hc, hcov⟩
  · haveI := hν₁
    refine ⟨?_, ?_⟩
    · obtain ⟨Ω', m, P', hP', Y₀, Y, hY₀m, hlaw, hY⟩ := HRS.A33.a33_exists_process S q hq ν₁
      exact ⟨Ω', m, P', hP', Y₀, Y, hY₀m, hlaw, ⟨hY.init, hY.meas, hY.gauss⟩⟩
    · intro Ω₁ Ω₂ _ _ P₁ P₂ _ _ Y₀₁ Y₀₂ Y₁ Y₂ hl₁ hl₂ h₁ h₂ p ts φ hts hφ
      exact HRS.A33.a33_unique S q e P₁ P₂ ν₁ Y₀₁ Y₀₂ Y₁ Y₂ hl₁ hl₂
        ⟨h₁.init, h₁.meas, h₁.gaussian_part⟩ ⟨h₂.init, h₂.meas, h₂.gaussian_part⟩ p ts φ hts hφ

end Main

end HRS
