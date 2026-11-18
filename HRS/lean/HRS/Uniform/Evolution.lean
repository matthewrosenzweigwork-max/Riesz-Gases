import HRS.Uniform.Comparison
import HRS.PDE.MeanFieldDefs

/-!
# Section 3 (evolution estimates at fixed temperature; stationary noise): specification statements, part III
(packet SPEC-U; all theorems here are statements with `sorry` proofs)

Rows (main manuscript `M`, source lines of `HRS_periodic_main_20261008T010000Z.tex`):

* Lemma 3.27 `M:P:lem:evolution` (L2531-2546): `evolution_estimates`.
* Lemma 3.31 `M:lem:stationary-noise` (L2758-2769): `stationary_noise`.

## Representation decisions (the orchestrator must check these against the TeX)

* **Setting of Lemma 3.27.**  The lemma sits in the subsection "Evolution estimates at a fixed positive temperature" (L2515),
  with the gradient mean-field dynamics of the finite-regularity statement Proposition 5.1 (L5771-5791;
  `HRS.PDE.FiniteRegHyp`, `HRS.PDE.IsMFSolutionHK`, `M = -I`, `ν = β⁻¹`, `HRS.PDE.mfData`), whose density path `ρ^t`
  converges exponentially to the thermal density; the TeX does not restate these hypotheses (it refers to
  `\\cref{sec:finite-regularity}`), so they are the hypotheses of the statement.
* **The evolution dual to the backward generator on `E_r`** is not a library object; it is characterised by duality
  with the classical adjoint propagator `HRS.propagator` (Definition 3.5): `⟨V^{t,u} z, φ⟩ = ⟨z, U^{u,t} φ⟩` for smooth `φ`
  (`IsDualEvolution`).  The lemma asserts that a strongly continuous evolution `V` on `E_r = H^{-r}_0` with this duality
  exists and satisfies the decay and maximal bounds (existence is the content "the evolution dual to
  `H:eq:backward-generator` is strongly continuous on `E_r`").
* **Stochastic convolutions and Hilbert martingales** as in `HRS/Uniform/Spec.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

universe u

variable {d : ℕ}

/-- `V` is the evolution dual to the backward generator `H:eq:backward-generator` (for the dynamics `D` and the density path
`ρ`) on `E_m = H^{-m}_0`: `⟨V^{t,u} z, φ⟩ = ⟨z, U^{u,t} φ⟩` for `0 ≤ u ≤ t`, `z ∈ E_m` and smooth `φ`, where `U^{u,t} =
HRS.propagator D ρ u t` is the adjoint propagator of Definition 3.5 and `⟨F, φ⟩ = NegSobolev.eval F φ`. -/
def IsDualEvolution (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m : ℝ)
    (V : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) : Prop :=
  ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ (z : NegSobolev d m) (φ : Torus d → ℝ), Torus.IsSmooth φ →
    NegSobolev.eval (V t u z) φ = NegSobolev.eval z (propagator D ρ u t φ)

/-- Lemma 3.27 (`M:P:lem:evolution`, "Maximal estimates and decay", TeX M L2531-2546), at a fixed positive temperature
`β` for the gradient mean-field flow of Proposition 5.1 (`FiniteRegHyp`, `IsMFSolutionHK`, the regularity index `K`
sufficiently large depending on `r`: "uniform smooth density and potential bounds", L2557-2558; for each real `r`).

(1) For each real `r` the evolution `V^{t,u}` dual to the backward generator is strongly continuous on `E_r` (a strongly
continuous evolution `Vev` with `IsDualEvolution` exists); (2) on the zero-mass subspace (all of `E_r = H^{-r}_0`)
`‖V^{t,u}‖_{E_r→E_r} ≤ C_r e^{-c_r(t-u)}`, `0 ≤ u ≤ t` (`P:eq:decay`); (3) for every `T > 0`, every continuous
`E_r`-valued martingale `M` with covariance density `C_u`, and every window `[a, a+T]`, `a ≥ 0`, the stochastic convolution
`∫_a^t V^{t,u} dM_u` has a continuous version with
`E sup_{a≤t≤a+T} ‖∫_a^t V^{t,u} dM_u‖²_{E_r} ≤ C_{r,T} E ∫_a^{a+T} Tr C_u du` (`P:eq:maximal`), with `C_{r,T}` independent of
`a` (chosen before `a`).  The two integrals are `lintegral`s in `ℝ≥0∞`.

"The same statements hold for the stationary evolution and for the Gaussian noise considered here": the stationary evolution
is the instance of this statement for the stationary solution `ρ^t ≡ ρ_β` (`ρ⁰ = ρ_β`, `FiniteRegHyp` holds for the smooth
positive thermal density), and Gaussian noise is a special case of a continuous martingale; neither is restated.

AMBIGUITY (L2515-2530): the regularity hypotheses are not restated in the lemma; the reading used is `FiniteRegHyp` with
`β₋ = β₊ = β` and `K ≥ K₀(r)`.  Technical hypotheses: as in Lemma 3.17 (separable `E_r`, `L²` martingale, `M_0 = 0`). -/
theorem evolution_estimates (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (r : ℝ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ (β : ℝ) (hβ : 0 < β) (V ρ₀ : Torus d → ℝ),
      PDE.FiniteRegHyp d s β β K V ρ₀ → ∀ ρc : ℝ → PDE.Coeff d,
      PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc →
      ∃ Cr cr : ℝ, 0 < Cr ∧ 0 < cr ∧
        ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
          IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (PDE.mfPath ρc) r Vev ∧
          (∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T) ∧
          (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr * Real.exp (-cr * (t - u))) ∧
          ∀ T : ℝ, 0 < T → ∃ CrT : ℝ, 0 ≤ CrT ∧
            ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
              ∀ (M : ℝ → Ω → NegSobolev d r) (Sg : ℝ → Ω → (NegSobolev d r →L[ℝ] NegSobolev d r →L[ℝ] ℝ)),
                IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
                ∃ Z : ℝ → Ω → NegSobolev d r,
                  (∀ t ∈ Set.Icc a (a + T),
                    IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d r)) M a t (Z t)) ∧
                  (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + T))) ∧
                  ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P ≤
                    ENNReal.ofReal CrT *
                      ∫⁻ ω, (∫⁻ u in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg u ω))) ∂P := by
  sorry

/-- Lemma 3.31 (`M:lem:stationary-noise`, "Periodic stationary noise on a fixed observation window", TeX M L2758-2769).
`μ = ρ_β dx` is a smooth positive periodic thermal equilibrium measure (`IsThermalDensity`, smooth, `ρ_β > 0`, `V` smooth).
`Q` is the actual stationary particle law (`Law X_t = Q` for all `t ≥ 0`) with `N Var_Q[μ_N(f)] ≤ C ‖f‖²_{L²(μ)}` for
`f ∈ L²(μ)` (`evariance`, in `ℝ≥0∞`) and `‖dm_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`, `m_N` the one-particle marginal of `Q`.
At every sufficiently large fixed negative Sobolev index `m` (`m ≥ m₀`), the empirical martingale `M` (an `E_m`-valued
martingale with covariance density `C_N^t = covForm m β⁻¹ (μ_N^t)`, i.e. the empirical martingale of Lemma 3.24 with
`σ_N = √N`, `q_N = β⁻¹`: the TeX's "`2β⁻¹μ`" covariance) and a Gaussian martingale `Ḡ` with covariance `D_t = covForm m β⁻¹ μ`
admit one adapted coupling (an enlargement, `Ḡ` independent of the initial σ-field `𝒢`, `M∘π - Ḡ` a Hilbert martingale; the
conjuncts of `IsAdaptedGaussianCoupling` for the whole half-line `T = ∞`), whose propagated difference
`Z_t = ∫_0^t V^{t,u} d(M - Ḡ)_u` (`V` the stationary dual evolution on `E_m`, `IsDualEvolution` for the frozen coefficient
`ρ_β`) has, on every window `[a, a+T]`, `a ≥ 0`, second-mean path norm
`‖sup_{a≤t≤a+T} ‖Z_t‖_{E_m}‖_{L²} ≤ C_T (N^{-1/2} + δ_N)`, uniformly in `a ≥ 0` (one coupling, one constant).
The index threshold `m₀` depends on `(d, s, β, V)` only; the constant `C_T` is chosen after `m`, the constant `Cv` of the hypotheses
(the TeX's generic `C`) and `T`, and before `N`, `δ_N` and everything on the probability space.  The second mean is a `lintegral` in `ℝ≥0∞`.

Representation: only the covariation of `M` and the stationarity/one-body estimates of the particle law are used (as in the
TeX proof, L2776-2799), so the particle process is the pair `(X, Q)` and `M` is any martingale with this covariation;
`V` is any evolution with the stationary duality (it exists, strongly continuous and exponentially decaying, by Lemma 3.27 for
the stationary solution).  AMBIGUITY: the "adjoint gap" (exponential decay of `V^{t,u}`, L2800-2801) is not a hypothesis here
because it is a consequence of the duality with the (frozen-coefficient) propagator (Lemma 3.27). -/
theorem stationary_noise (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (_ : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (_ : IsThermalDensity (periodicRiesz d s) V β ρβ) (_ : Torus.IsSmooth ρβ) (_ : ∀ x, 0 < ρβ x) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ Cv : ℝ, ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (N : ℕ) (_ : 1 ≤ N) (δ : ℝ) (_ : 0 ≤ δ)
        (X : ℝ → Ω → Config d N) (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (_ : ∀ t : ℝ, 0 ≤ t → P.map (X t) = Q)
        (_ : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
          evariance (fun x : Config d N => pair (empirical x) f) Q ≤
            ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)))
        (g : Torus d → ℝ) (_ : Measurable g)
        (_ : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
          (withDensityReal ρβ).withDensity fun x => ENNReal.ofReal (g x))
        (_ : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρβ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2))
        (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
        (_ : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
        (M : ℝ → Ω → NegSobolev d m)
        (_ : ∀ S : ℝ, 0 ≤ S →
          IsHilbertMartingaleWithCovariation P ℱ S M
            (fun r ω => covForm m β⁻¹ (empirical (X r ω)))),
        ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω') (π : Ω' → Ω)
          (ℱ' : Filtration ℝ mΩ') (Gb : ℝ → Ω' → NegSobolev d m)
          (Sd : ℝ → Ω' → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ))
          (Z : ℝ → Ω' → NegSobolev d m),
          IsAdaptedGaussianCoupling P ℱ ⊤ 𝒢 M (fun r ω => covForm m β⁻¹ (empirical (X r ω)))
            (fun r => covForm m β⁻¹ (withDensityReal ρβ)) (fun _ _ => True) (fun _ _ => 0)
            P' π ℱ' Gb Sd ∧
          (∀ t : ℝ, 0 ≤ t → IsStochConv (P' : Measure Ω') Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
            (fun τ ω' => M τ (π ω') - Gb τ ω') 0 t (Z t)) ∧
          (∀ᵐ ω' ∂(P' : Measure Ω'), ContinuousOn (fun t => Z t ω') (Set.Ici 0)) ∧
          ∀ a : ℝ, 0 ≤ a →
            (∫⁻ ω', (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω'‖ₑ) ^ 2 ∂(P' : Measure Ω')) ^ (1 / 2 : ℝ) ≤
              ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 2) + δ)) := by
  sorry

end Uniform

end HRS
