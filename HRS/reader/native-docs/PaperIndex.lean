import HRS.Main.TSGFinal
import Verso
import VersoManual
import VersoBlueprint
open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Browse the paper and supplement" =>

%%%
tag := "paper-index"
%%%

The paper and supplement contain 24 top-level headings and 143 subsections. Eight selected entries below link to Lean declarations; the detailed chapters develop the sharp commutator estimate and the mesoscopic comparison. The remaining headings retain the manuscript’s organization.

# 1. Introduction
%%%
tag := "section-M-1"
%%%

Main paper, lines 159–415.

* Initial fluctuations and thermal noise
* Evolution, equilibrium, and the choice of center
* The first correction and observations at changing scales
* Periodic dynamics and confinement on the whole space
* Related work

# 2. Main results and proof strategy
%%%
tag := "section-M-2"
%%%

Main paper, lines 416–1467.

* Conventions, centerings, and the linear equation
* The general fluctuation scale
* Prepared nonequilibrium fluctuations and thermalization
* Equilibrium fluctuations and the marginal bias
* Uniformity over the window start
* Bounded spectral interactions
* Mesoscopic covariance formation
* Proof strategy

## Fluctuations at varying temperature and initial scale
%%%
tag := "sample-1"
%%%

Main paper theorem 2.1 · selected declaration. Selected Lean declaration

*Recorded formal verification pass*. 

Declaration: `HRS.GeneralSetup.general_fluctuation_proof`.

Source: [`HRS/Main/GFFinal.lean`](source/HRS/Main/GFFinal.lean), line 12.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem general_fluctuation_proof : type_of% @HRS.GeneralSetup.general_fluctuation :=
  @HRS.GF.gff_general_fluctuation

theorem general_fluctuation_transport_proof : type_of% @HRS.GeneralSetup.general_fluctuation_transport :=
  @HRS.GF.gff_general_fluctuation_transport
```
Recorded verification: theorem check passed.

# 3. General fluctuation evolution
%%%
tag := "section-M-3"
%%%

Main paper, lines 1468–3338.

{ref "commutator"}[Read the sharp commutator theorem]

* The finite-N fluctuation identity
* The adjoint linearized flow on the torus
* Comparison of complete stochastic paths
* Energy and transport bounds for the particle noise
* A covariance coupling with a quadratic error
* Modulated-energy estimates
* Higher heat-filter orders and the general theorem
* The physical high-temperature endpoint

# 4. Equilibrium fluctuations and centering
%%%
tag := "section-M-4"
%%%

Main paper, lines 3339–5761.

* The thermal equilibrium measure
* The heat decomposition and conditional variance
* Calibration of the finite positive part
* The marginal and centered quadratic estimates
* The leading bias and its nonvanishing coefficient
* Stationarity, finite history, and the stronger topology
* Static inputs and conditioning
* The conditional singular observation
* Identification of the critical response
* Critical temporal cancellation
* The weak reference and a pointwise pin comparison
* Pair and three-particle moment estimates
* The two-particle Poisson equation
* The diagonal inverse and the global correction
* The lifted generator identity
* The continuous-path estimate
* Bounded positive spectral kernels, including negative Riesz exponents
* Preparation and the zero endpoint
* Deterministic translations and the critical rate

## Small polynomial loss in product moment transfer
%%%
tag := "sample-2"
%%%

Main paper lemma 4.4 · selected declaration. Selected Lean declaration

*Recorded formal verification pass*. 

Declaration: `HRS.product_moment_transfer_proof`.

Source: [`HRS/Equilibrium/ProductTransfer.lean`](source/HRS/Equilibrium/ProductTransfer.lean), line 752.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem product_moment_transfer_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 2 ≤ q ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ Y : Config d N → ℝ, Measurable Y →
        eLpNorm Y 2 (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞) (Measure.pi fun _ : Fin N => withDensityReal ρ)) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ Y : Config d (N - 1) → ℝ, Measurable Y →
        eLpNorm Y 2 (critPole d s c β ρ N x t) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ ε) *
            eLpNorm Y ((2 * q : ℕ) : ℝ≥0∞)
              (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ)) := by
  exact product_moment_transfer_real hd hcrit β hβ ρ hρ c hc

example := (@product_moment_transfer_proof : type_of% @product_moment_transfer)

end HRS
```
Recorded verification: Comparator statement-equivalence check passed.

# 5. Evolving fluctuations and thermalization
%%%
tag := "section-M-5"
%%%

Main paper, lines 5762–7555.

* A finite-regularity periodic relaxation statement
* The weighted adjoint and the long-time covariance
* Fluctuations away from equilibrium
* Pressure bounds stable under singular pair perturbations
* Entropy along a nonstationary reference
* Verification under the evolving particle law
* Equilibrium-relative laws and exact centering
* An exact criterion for the remaining full-range theorem
* Why centering alone cannot supply the estimate
* A nonzero nonlinear mean transient
* Why the global unweighted supremum is not the state space

## Nonequilibrium fluctuation comparison
%%%
tag := "sample-3"
%%%

Main paper proposition 5.4 · selected declaration. Selected Lean declaration

*Recorded formal verification pass*. 

Declaration: `HRS.dynamic_comparison_proof'`.

Source: [`HRS/Sections/DynCmpFinal2.lean`](source/HRS/Sections/DynCmpFinal2.lean), line 23.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem dynamic_comparison_proof' (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (T : ℝ) (hT : 0 ≤ T) (p : ℕ)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn T X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ t : Fin p → ℝ, (∀ a, t a ∈ Set.Icc (0 : ℝ) T) →
        ∀ G : Ω → EuclideanSpace ℝ (Fin p),
          law P G = ProbabilityTheory.multivariateGaussian 0 (noiseCovMatrix htr.dyn ρ β⁻¹ t φ) →
          AEMeasurable G P →
          ProbabilityTheory.IndepFun X₀ G P →
          smoothDist 2
              (law P fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ (t a))) (φ a) (X (t a).toNNReal ω) :
                  EuclideanSpace ℝ (Fin p)))
              (law P fun ω => (WithLp.toLp 2 fun a =>
                linCoord (withDensityReal (ρ 0)) (propagator htr.dyn ρ 0 (t a) (φ a)) (X₀ ω) + G ω a :
                  EuclideanSpace ℝ (Fin p))) ≤
            C * (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / Real.sqrt N +
                Real.sqrt (entropyScale d s N (P.map X₀)
                  (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) := by
  have hd1 : 1 ≤ d := by omega
  have htr' : MovTraj htr.dyn T ρ :=
    movT_traj_of_global_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global T
  obtain ⟨c₀, Λ₂, hc₀, hb⟩ :=
    movT_traj_uniform_proof s β V ρ₀ ρ htr.hs0 htr.hsd htr.hβ htr.V_smooth htr.init htr.global
```
Recorded verification: Comparator statement-equivalence check passed.

# 6. Mesoscopic observations and screening
%%%
tag := "section-M-6"
%%%

Main paper, lines 7556–7720.

{ref "screening"}[Read the whole section]


## Uniform comparison and explicit observation scales
%%%
tag := "sample-4"
%%%

Main paper proposition 6.1 · selected declaration. Selected Lean declaration

*Recorded formal verification pass*. 

Declaration: `HRS.screening_comparison_proof`.

Source: [`HRS/Sections/ScrnFinal.lean`](source/HRS/Sections/ScrnFinal.lean), line 21.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem screening_comparison_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hsd : s < d) (p : ℕ) (φ : Fin p → Euc d → ℝ)
    (hφ : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (φ a) ∧ HasCompactSupport (φ a)) (x₀ : Euc d)
    (bm bp : ℝ) (hbm : 0 < bm) (hbmp : bm ≤ bp) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 ≤ C ∧
      (∀ N : ℕ, 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (volume : Measure (Torus d)) + oN d s C₀ N) ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (βN : ℝ) (hβN : 0 < βN) (ℓ b : ℝ), 0 < ℓ →
        βN * ℓ ^ ((d : ℝ) - s) ∈ Set.Icc bm bp → b ∈ Set.Icc bm bp →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          IsVectorBrownian P W →
          ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P →
          P.map X₀ = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))) →
          (∀ T' : ℝ, 0 ≤ T' →
            IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) βN hβN) T' X₀ W X) →
          (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
            (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
          ∀ t : Fin p → ℝ, (∀ a, 0 ≤ t a) →
            smoothDist 3
                (law P fun ω => (WithLp.toLp 2 fun a =>
                  linCoord (volume : Measure (Torus d)) (mesoTest d ℓ x₀ (φ a))
                    (X (ℓ ^ (2 - ((d : ℝ) - s)) * t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
                (ProbabilityTheory.multivariateGaussian 0 (mesoCovMatrix d s b t φ)) ≤
              C * ((N : ℝ) ^ (-(1 : ℝ) / 2) * ℓ ^ (-(d : ℝ) / 2) +
                Real.sqrt N * oN d s C₀ N * ℓ ^ (-(d : ℝ) / 2 - max ((d : ℝ) - s) 2) +
                (N : ℝ) ^ (-(1 : ℝ) / d) * ℓ ^ (-(d : ℝ) - 3 + min ((d : ℝ) - s) 2) +
                Real.sqrt (oN d s C₀ N) *
                  ℓ ^ (-((d : ℝ) + ((d : ℝ) - s)) / 2 - 2 + min ((d : ℝ) - s) 2) +
                ℓ + |βN * ℓ ^ ((d : ℝ) - s) - b|) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₀, Cq, hC₀, hCq, hcom⟩ := HRS.Main.A8P.a8p_commSpec hd1 hs0 hsd
  obtain ⟨C1, hC1, hinst⟩ := scrn_instance hd hs0 hsd φ hφ x₀ hbm hbmp hC₀ hcom hCq.le
  refine ⟨C₀, max C1 2, hC₀, le_max_of_le_right (by norm_num), ?_, ?_⟩
  · intro N hN X hX
```
Recorded verification: Comparator statement-equivalence check passed.

# 7. The first correction on observation windows
%%%
tag := "section-M-7"
%%%

Main paper, lines 7721–10001.

* The independent initial expansion
* Dimension-free Gaussian identities
* Static quadratic statistics and the cubic coefficient
* Quadratic fluctuations in the Hilbert–Schmidt range
* The static second-chaos limit
* Proof of the static correction
* Field-valued quadratic limits
* Moment and analytic estimates in a common field space
* Static Edgeworth expansion on a Hilbert space
* Uniform moment transfer and quadratic fields
* The Lipschitz seminorm in the moving source
* Uniform windows for the field and its second chaos
* Entropy identities without an inverse-Gibbs moment
* Causal vector measures on the continuous-path space
* The drift measure
* Covariance measures for signed distribution-valued coefficients
* A dimension-free path interpolation identity
* Strong convergence of the correction data
* Removing the conditioning in the limiting integrals
* Identification with the finite-dimensional formula
* The uniform shifted-window expansion
* Stationary limits and the two-parameter expansion
* A change of preparation temperature
* First corrections with non-Gaussian initial fluctuations
* The instantaneous quadratic commutator at the Hilbert–Schmidt threshold

# A. Lower-regularity observations and initial data
%%%
tag := "section-M-A"
%%%

Main paper, lines 10002–11624.

* The model and functional setting
* The periodic potential
* Fluctuation theorems
* Quantitative central limit theorems for continuous martingales
* Proofs of the fluctuation theorems
* Initial data and admissible fluctuation scales

# B. Particle dynamics and the entropy inequality
%%%
tag := "section-M-B"
%%%

Main paper, lines 11625–12220.

* Particle processes and their time-marginal laws
* Direct collision-free regimes
* The maximal solution obtained by force truncation
* Cluster dispersion
* A logarithmic barrier and descending induction over clusters
* The one-dimensional power-Riesz pair barrier
* Conclusion of the strong well-posedness proof
* Selected gradient laws: Gibbs entropy and entropy admissibility

# C. Auxiliary lemmas
%%%
tag := "section-M-C"
%%%

Main paper, lines 12221–12339.


## Square roots of nonnegative C¹,¹ functions
%%%
tag := "sample-5"
%%%

Main paper Lemma C.6 · torus gradient clause.

:::theorem "index-c6-provider" (lean := "HRS.Main.torus_sqrt_gradient_le_proof")
Let $`\mathsf d\in\mathbb N` and $`L\geq0`. Let $`a:\mathbb T^{\mathsf d}\to[0,\infty)` have a continuously differentiable periodic lift $`A(x)=a(x\bmod\mathbb Z^{\mathsf d})` whose derivative is $`L`-Lipschitz in operator norm. Then $`u=\sqrt A` is differentiable almost everywhere and satisfies

$$`\|Du(x)\|\leq\sqrt{L/2}`

at every point of differentiability. In particular,

$$`\mathop{\mathrm{ess\,sup}}_{x\in\mathbb R^{\mathsf d}}\|Du(x)\|\leq\sqrt{L/2}.`

*Proof outline.* The square-root Lipschitz estimate gives $`\operatorname{Lip}(u)\leq\sqrt{L/2}`, hence almost-everywhere differentiability. At a point where $`A>0`, the chain rule and the directional estimate

$$`|DA(x)h|^2\leq2L A(x)\|h\|^2`

give the asserted derivative bound. At a zero of $`A`, the nonnegative function $`u` has a minimum, so its derivative vanishes whenever it exists. The essential-supremum estimate follows. All almost-everywhere statements and the essential supremum use Lebesgue measure.
:::

[Full Lean source](source/HRS/Main/TSGFinal.lean).

# D. Smooth scale truncation of the interaction
%%%
tag := "section-M-D"
%%%

Main paper, lines 12340–12644.

* The representation and the truncation
* Comparison, coercivity, and the Itô bound
* The truncated commutator estimate

## Truncated commutator
%%%
tag := "sample-6"
%%%

Main paper lemma D.6 · selected declaration. Selected Lean declaration

Statement only (the Lean source uses `sorry`). For the sharp estimate used in §6, see [The sharp sub-Coulomb commutator](reader-anchor:commutator).

Declaration: `HRS.fdl_commutator`.

Source: [`HRS/Appendix/FDL.lean`](source/HRS/Appendix/FDL.lean), line 381.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem fdl_commutator (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → smearScale d N Λ < 1 / 2 →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (u : Torus d → Euc d) (K : ℝ), HasTransportBound d s u K →
      ∀ η : ℝ, smearScale d N Λ ≤ η → η < 1 →
        |commQuantityWith (Torus.grad (fdlTruncT ψ s b η)) u X (withDensityReal ρ)| ≤
          C * K * (fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  sorry

/-! ### Remark D.7: scope -/

/-- Remark D.7 (`M:B:rem:fdl-scope`, TeX M L12477-12479), the checkable content: the statements of
```
Verification status: stated only; no proof claimed.

# S1. Whole-space fluctuations and the noncompact estimates
%%%
tag := "section-S-S1"
%%%

Whole-space supplement, lines 156–259.

* Statements, normalization, and proof dependencies

# S2. Statement of the confined fluctuation results
%%%
tag := "section-S-S2"
%%%

Whole-space supplement, lines 260–472.


## Whole-space Edgeworth expansion (part iii)
%%%
tag := "sample-7"
%%%

Supplement Theorem S2.1(iii) · selected declaration. Selected Lean declaration

*Recorded formal verification pass*. 

Declaration: `HRS.Whole.whole_space_edgeworth`.

Source: [`HRS/MS/Fp81S21WholeSpaceEdgeworth.lean`](source/HRS/MS/Fp81S21WholeSpaceEdgeworth.lean), line 45.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem whole_space_edgeworth (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀s : 0 < s → 0 < β₀)
    (T : ℝ) (hT : 0 < T) (c₁ C₁ : ℝ) :
    ∃ εstar : ℝ, 0 < εstar ∧
      ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ ε : ℝ, ∀ ψ : Euc d → ℝ,
        IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc d → ℝ,
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∃ (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3) (εN : ℕ → ℝ),
          (∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖κ a₀‖ ≤ Kb) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
            (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
            (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) (M.domDomCongr σ) =
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M) ∧
          Tendsto εN atTop (𝓝 0) ∧
          (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
            (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
            (∃ χ : Fin 3 → ℝ → Euc d → ℝ,
              ∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
                MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
                ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                  Integrable (fun x => ψ' x * χ i r x) ∧
                  ∫ x, ψ' x * χ i r x = linearGaussianCov
                    ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                    (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                    ψ' (φ i)) ∧
            ∀ χ : Fin 3 → ℝ → Euc d → ℝ,
            (∀ i, ∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T),
              MemLp (fun x => χ i r x / ρ r x) 2 (withDensityReal (ρ r)) ∧
              ∀ ψ', IsOscTest (wholeSpaceIndex d) ψ' →
                Integrable (fun x => ψ' x * χ i r x) ∧
                ∫ x, ψ' x * χ i r x = linearGaussianCov
                  ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
                  (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) r (a₀ + τ i)
                  ψ' (φ i)) →
            ∀ M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ,
              (∀ w : Fin 3 → OscPath d (wholeSpaceIndex d) T,
                M w = ∏ i, OscDual.eval (OscPath.at' (w i) (τ i)) (φ i)) →
              (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M =
                cubicFormula (quadraticGradientDyn d s a β) ρ β β₀ (withDensityReal (ρ 0))
                  (fun i => a₀ + τ i) φ χ ∧
              CubicFormulaIntegrable (quadraticGradientDyn d s a β) ρ β₀ (withDensityReal (ρ 0))
                (fun i => a₀ + τ i) φ χ) ∧
          ∀ N : ℕ, 2 ≤ N →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
            (X : ℝ≥0 → Ω → EucConfig d N),
            IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
            law P X₀ = modulatedGibbs (rieszKernel d s) N β₀ (withDensityReal (ρ 0)) →
            (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn d s a β) T' X₀ W X) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
            (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
              (wholeSpaceIndex d) β⁻¹ T'
              (susceptibilityCov (rieszKernel d s) (withDensityReal (ρ 0)) β₀) Z) →
          ∀ a₀ : ℝ, 0 ≤ a₀ →
            AEMeasurable (zetaPathW (wholeSpaceIndex d) T a₀ P X) P ∧
            AEMeasurable (processWindow (wholeSpaceIndex d) T a₀ Z) P' ∧
            ∀ Φ : OscPath d (wholeSpaceIndex d) T → ℝ,
              Φ ∈ CbUnitBall (OscPath d (wholeSpaceIndex d) T) 5 →
              |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T a₀ P X ζ) ∂P -
                  ∫ ζ', Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ') ∂P') -
                (1 / 6) * ∫ ζ', (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
                  (iteratedFDeriv ℝ 3 Φ (processWindow (wholeSpaceIndex d) T a₀ Z ζ')) ∂P'| ≤
                εN N :=
  @HRS.Fp81.S21.fp81s21_whole_space_edgeworth d hd s hs0 hs a β ha hβ β₀ hβ₀ hβ₀s T hT c₁ C₁

end HRS.Whole
```
Recorded verification: theorem check passed.

# S3. Pressure and calibrated equilibrium estimates
%%%
tag := "section-S-S3"
%%%

Whole-space supplement, lines 473–2030.

* Singular pressure without compact support
* The positive Riesz equilibrium estimates on the whole space
* The logarithmic Gibbs estimates under quadratic confinement
* The static Gaussian comparison step

# S4. Thermal fields and support-independent correctors
%%%
tag := "section-S-S4"
%%%

Whole-space supplement, lines 2031–3189.

* Exactly centered static fields under quadratic confinement
* Decay of adjoint tests and the sharp sub-Coulomb commutator
* Whole-field paths from bounded adjoint orbits

## Far-field derivatives of the nonlocal term
%%%
tag := "sample-8"
%%%

Supplement lemma S4.10 · selected declaration. Selected Lean declaration

*Recorded formal verification pass*. 

Declaration: `HRS.Whole.far_derivatives_proof`.

Source: [`HRS/MS/SuppU2.lean`](source/HRS/MS/SuppU2.lean), line 17.

Exact source excerpt. It may include adjacent declarations or end before the proof does; open the source file for full context.

```
theorem far_derivatives_proof : type_of% @HRS.Whole.far_derivatives := by
  intro d hd s hs0 hsd k L hL
  exact ⟨u2_partA hd s hs0 hsd k L hL, fun M Λρ => u2_partB hd s hs0 hsd k L hL M Λρ⟩

end HRS.Whole
```
Recorded verification: theorem check passed.

# S5. Weighted paths and general fluctuation scales
%%%
tag := "section-S-S5"
%%%

Whole-space supplement, lines 3190–4147.

* Varying temperature and arbitrary initial normalization

# S6. Nonlinear mean-field relaxation and exact moving families
%%%
tag := "section-S-S6"
%%%

Whole-space supplement, lines 4148–5256.

* Nonlinear relaxation near quadratic equilibrium
* Exact moving families for the full interacting particle system
* Particle fluctuation theorems in a quadratic potential

# S7. The whole-space marginal bias
%%%
tag := "section-S-S7"
%%%

Whole-space supplement, lines 5257–6208.

* The marginal expansion
* Static inputs and whole-space convolution estimates
* Uniform control of the conditional empirical potential
* The insertion pressure at the repulsion scale
* Solving the first-marginal response
* Quadratic confinement and the sharp centering threshold

# S8. Critical stationary fluctuations
%%%
tag := "section-S-S8"
%%%

Whole-space supplement, lines 6209–6770.

* The critical coefficient and the stationary path estimate
* Weighted verification of the critical centered forcing
* A weighted global inverse in the quadratic geometry
* Whole-space localization and the maximal noise estimate
* The distant past and the stationary comparison

# S9. Singular moments and the field correction
%%%
tag := "section-S-S9"
%%%

Whole-space supplement, lines 6771–7696.

* Singular moment transfer with a vanishing density
* Polynomially weighted moments in the Hilbert–Schmidt range
* The interacting static field correction

# S10. The weighted path correction
%%%
tag := "section-S-S10"
%%%

Whole-space supplement, lines 7697–8488.

* Signed covariance measures on the whole-space path space
* Interacting continuous-path Edgeworth corrections
* Leading fluctuations uniformly over fixed observation windows

# S11. Uniform windows and moving mean-field measures
%%%
tag := "section-S-S11"
%%%

Whole-space supplement, lines 8489–9631.

* Uniform shifted windows and relaxation of the correction
* Corrections along a nonstationary mean-field trajectory
* Independent logarithmic preparation

# S.A. Unconfined and general whole-space comparisons
%%%
tag := "section-S-S.A"
%%%

Whole-space supplement, lines 9632–11076.

* Uniformly local tests and their interpretation
* Confinement and trajectory assumptions
* Weighted trajectory assumptions for the general comparison
* Initial statistics in the uniformly local class
* The whole-space linear comparison field
* The confined finite-particle process
* Entropy admissibility under confinement
* The adjoint linearized flow on the whole space
* Qualitative convergence on path space
* Uniformly local spaces and transported cutoffs

# S.B. Further whole-space comparison estimates
%%%
tag := "section-S-S.B"
%%%

Whole-space supplement, lines 11077–11595.

* Modulated free energy under general confinement
* Transported initial fields on the whole space
* Whole-space kernel bounds
* Whole-space commutator estimates
* Complementary whole-space energy estimates
* The transported initial-field hypothesis
* The whole-space limit field
* Weighted same-function symmetrization

