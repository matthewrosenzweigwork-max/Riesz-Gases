import HRS.Uniform.Spec
import HRS.Energy.Coercivity
import HRS.Energy.StaticLimitGauss
import HRS.PDE.Convention
import HRS.Uniform.Q12Aux7

/-!
# Section 3 (comparison of complete stochastic paths): specification statements, part II
(packet SPEC-U; all theorems here are statements with `sorry` proofs)

Rows (main manuscript `M`, source lines of `HRS_periodic_main_20261008T010000Z.tex`):

* Lemma 3.22 `M:U:lem:filtered` (L2266-2276): `filtered_coercivity`.
* Lemma 3.23 `M:U:lem:energy-W2` (L2354-2361): `energy_W2`.
* Lemma 3.24 `M:U:lem:transport-noise` (L2396-2405): `transport_noise_coupling`.
* Remark after Theorem 2.1's proof, "Higher Wasserstein orders" `M:@remark:L2482` (L2482-2496):
  `general_fluctuation_Wp`.
* Corollary 3.26 `M:U:cor:coefficients` (L2498-2511): `coefficient_comparison`.
* Proposition 3.28 `M:P:prop:comparison` (L2603-2641): `comparison_smooth`, `comparison_wasserstein`.
* Lemma 3.29 `M:R:lem:relative-covariance` (L2682-2695): `relative_covariance_cost`,
  `relative_covariance_coupling`.
* Lemma 3.30 `M:R:lem:chart-current` (L2731-2742): `chart_current`.

(Lemma 3.27 `M:P:lem:evolution` and Lemma 3.31 `M:lem:stationary-noise` are in `HRS/Uniform/Evolution.lean`.)

## Representation decisions (the orchestrator must check these against the TeX)

* **The covariances `C_N^t`, `C̄_N^t`** (`U:eq:particle-covariances`, L2290-2293) are `covForm γ q μ`:
  `2q ∑_j ∫ b_{x,j} ⊗ b_{x,j} dμ(x)` as a bounded bilinear form on `H = H^{-γ}_0` (`NegSobolev d γ`),
  with `b_{x,j} = -∂_j δ_x ∈ H` (`bVec`; its coefficients against the real basis `e_k` are `∂_j e_k(x)`;
  this lies in `H` for `γ > d/2 + 1`) and `μ = μ_N^t` (empirical measure) respectively `μ^t`.  The Bochner
  integral `outerCov` is taken in the Banach space of bounded bilinear forms; the integrand is norm-continuous
  in `x` for `γ > d/2 + 2` so it is the honest integral.  `‖·‖_{𝔖₁}` is `HRS.traceNormForm`.
* **"Adapted coupling of the entire martingales"** (Lemmas 3.19, 3.24, 3.29, 3.31): `AdaptedGaussianCoupling`:
  an enlargement `(Ω', P', π, ℱ')` of the filtered space (ISSUES §G.1), on which the original martingale `M∘π` is
  still a Hilbert martingale with the same covariation, a Hilbert martingale `Ḡ` with *deterministic* covariation
  `D̄_r` (equivalently a Gaussian martingale of covariance `D̄_r dr`; Lévy) independent of the initial σ-field
  `𝒢 ⊆ ℱ_0`, and such that the difference `M∘π - Ḡ` is a Hilbert martingale whose covariation density has trace
  related (`≤` or `=`) to the prescribed cost, for a.e. `ω'` and all `r`.
* **`W_2` on the flat torus** (`torusWassersteinE`): infimum over couplings of the `ℝ≥0∞`-valued cost
  `(∫ |x-y|²)^{1/2}` with `|x-y| = Torus.tdist` the Euclidean quotient distance.  (`HRS.wassersteinE` is for normed
  vector spaces; the torus is not one.)
* **Heat-kernel completion** `𝓔_N = F_N(X_N, μ) + o_N` with `F_N = rieszEnergy` and `o_N = HRS.oN d s C₀ N`
  (`H:eq:energy-completion`); "sufficiently large completion" is `∃ C₀min, ∀ C₀ ≥ C₀min`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

universe u

variable {d : ℕ}

/-! ### The flat-torus Wasserstein distance and the covariances of the particle noise -/

/-- `W_p` on the flat torus `𝕋^d` (quadratic transport distance for `p = 2`): the infimum over couplings
`π` of `μ` and `ν` of `(∫ |x-y|^p dπ)^{1/p}`, `|x - y| = Torus.tdist x y`; `∞` if no coupling has finite
cost (it never is, the torus being compact). -/
def torusWassersteinE (p : ℝ) (μ ν : Measure (Torus d)) : ℝ≥0∞ :=
  ⨅ π : {π : Measure (Torus d × Torus d) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν},
    (∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ p) ∂π.1) ^ (1 / p)

/-- The vector `b_{x,j} = -∂_j δ_x ∈ H^{-γ}_0` (L2285): `⟨b_{x,j}, φ⟩ = ∂_jφ(x)`; its coefficient against the real
basis `e_k` is `∂_j e_k(x)`.  (It lies in `E_γ` for `γ > d/2 + 1`; for smaller `γ` the junk value `0` of
`NegSobolev.ofSeq` is taken, a case excluded by every statement below.) -/
def bVec (γ : ℝ) (j : Fin d) (x : Torus d) : NegSobolev d γ :=
  NegSobolev.ofSeq γ fun k => Torus.partialDeriv j (Torus.realMode k) x

/-- `∫ b(u) ⊗ b(u) dμ(u)` as a bounded bilinear form on `H`: the Bochner integral, in the Banach space
`H →L H →L ℝ`, of `u ↦ ⟨b(u), ·⟩⟨b(u), ·⟩`. -/
def outerCov {X : Type*} [MeasurableSpace X] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (b : X → H) (μ : Measure X) : H →L[ℝ] H →L[ℝ] ℝ :=
  ∫ u, (innerSL ℝ (b u)).smulRight (innerSL ℝ (b u)) ∂μ

/-- The particle-noise covariance `2q ∑_j ∫ b_{x,j} ⊗ b_{x,j} dμ(x)` on `H = H^{-γ}_0`
(`U:eq:particle-covariances`, L2290-2293): `C_N^t` for `μ = μ_N^t`, `C̄_N^t` for `μ = μ^t`; `q = q_N`. -/
def covForm (γ q : ℝ) (μ : Measure (Torus d)) : NegSobolev d γ →L[ℝ] NegSobolev d γ →L[ℝ] ℝ :=
  (2 * q) • ∑ j : Fin d, outerCov (bVec γ j) μ

/-! ### Lemmas 3.22 and 3.23: coercivity with heat filtering, and the transport bound -/

/-- Lemma 3.22 (`M:U:lem:filtered`, "Heat-filtered coercivity", TeX M L2266-2276), `q = d - s`.
Let `μ_X = N⁻¹∑δ_{x_i}` (pairwise distinct) and `μ = ρ dx` with `‖ρ‖_∞ ≤ Λ`.  For the sufficiently large completion
`𝓔_N = F_N + o_N` of `H:eq:energy-completion` (`≥ 0`, asserted), and every fixed integer `L ≥ 1`,
`|(μ_X - μ)(φ)| ≤ C_L ‖φ‖_{Ḣ^{q/2}} 𝓔_N^{1/2} + C_L N^{-2L/d} ‖Δ^Lφ‖_∞` (`U:eq:filtered`).  The constants depend
on `(d, s, Λ, L)` only (and `C₀min` on `(d,s,Λ)`).  `φ ∈ C^{2L}` with finite `Ḣ^{q/2}` seminorm (finiteness of the
displayed norm, as in `HRS.periodic_coercivity`); `‖Δ^Lφ‖_∞` is expressed by an arbitrary bound `A` (as `IsLipschitz`
in `periodic_coercivity`).

AMBIGUITY (L2268-2271): "For the sufficiently large completion … and every fixed integer `L`": read as one
threshold `C₀min` serving all `L` (the proof, L2279-2299, uses `L` only after fixing the completion), then
`∃ C_L` for each `L`.
Technical hypotheses: `d ≥ 1`, `N ≥ 2`, `X` collision-free (the `F_N` of the source is the off-diagonal energy). -/
theorem filtered_coercivity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ L : ℕ, 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N ∧
        ∀ φ : Torus d → ℝ, Torus.IsCk (2 * L : ℕ) φ → HasFiniteHomSobolev (((d : ℝ) - s) / 2) φ →
          ∀ A : ℝ, 0 ≤ A → (∀ x, |((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) x| ≤ A) →
            |∫ x, φ x ∂(empirical X) - ∫ x, φ x ∂(withDensityReal ρ)| ≤
              C * homSobolev (((d : ℝ) - s) / 2) φ *
                  Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) +
                C * (N : ℝ) ^ (-(2 * (L : ℝ)) / d) * A := by
  exact HRS.Uniform.Q12.filtered_coercivity_proof hd s hs0 hsd Λ

/-- Lemma 3.23 (`M:U:lem:energy-W2`, "Transport controlled by the completed energy", TeX M L2354-2361), in the
setting of Lemma 3.22: if also `ρ ≥ m₀ > 0`, then
`W_2(μ_X, μ) ≤ C (N^{-1/d} + 𝓔_N^{1/max(2,q)})`, `q = d - s`, with `W_2` the quadratic transport distance on the
flat torus (`torusWassersteinE 2`, in `ℝ≥0∞`; the displayed bound is finite).  The constant depends on
`(d, s, Λ, m₀)`.  Technical: as in Lemma 3.22; `𝓔_N ≥ 0` is asserted (so the power is not a junk value). -/
theorem energy_W2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ m₀ : ℝ) (hm₀ : 0 < m₀) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → (∀ x, m₀ ≤ ρ x) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N ∧
        torusWassersteinE 2 (empirical X) (withDensityReal ρ) ≤
          ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) ^ ((1 : ℝ) / max 2 ((d : ℝ) - s)))) := by
  sorry

/-! ### Lemma 3.24: transport-plan coupling of empirical and continuum noise -/

/-- "Adapted coupling of the entire martingales": an enlargement `(Ω', P', π, ℱ')` of the filtered probability space on
which (i) `M∘π` is still a Hilbert martingale for `ℱ'` with covariation `Sg∘π`, (ii) there is a Hilbert martingale `Ḡ`
with deterministic covariation `Db` (a Gaussian martingale of covariance `Db_r dr`), independent of the initial σ-field
`𝒢 ⊆ ℱ_0` (pulled back along `π`), and (iii) the difference `M∘π - Ḡ` is a Hilbert martingale with some covariation
density `Sd` whose trace `‖Sd_r‖_{𝔖₁}` satisfies `rel (‖Sd_r(ω')‖_{𝔖₁}) (cost r (π ω'))` for a.e. `ω'` and all `r`
(`rel` is `≤` or `=`).  The time horizon `T ∈ [0,∞]` is a bound for all the times considered; `T = ∞` is the whole half-line
(all the conditions hold on every `[0,S]`).  (Cf. the shape of `HRS.hilbert_polar_coupling`, Corollary A.23.) -/
structure IsAdaptedGaussianCoupling {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (T : ℝ≥0∞) (𝒢 : InitialSigma ℱ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ))
    (rel : ℝ → ℝ → Prop) (cost : ℝ → Ω → ℝ)
    {Ω' : Type u} {mΩ' : MeasurableSpace Ω'} (P' : ProbabilityMeasure Ω') (π : Ω' → Ω)
    (ℱ' : Filtration ℝ mΩ') (Gb : ℝ → Ω' → H) (Sd : ℝ → Ω' → (H →L[ℝ] H →L[ℝ] ℝ)) : Prop where
  preserving : MeasurePreserving π (P' : Measure Ω') P
  filtration : ∀ τ, (ℱ τ).comap π ≤ ℱ' τ
  martingale : ∀ S : ℝ, 0 ≤ S → ENNReal.ofReal S ≤ T →
    IsHilbertMartingaleWithCovariation (P' : Measure Ω') ℱ' S
      (fun τ ω' => M τ (π ω')) (fun r ω' => Sg r (π ω'))
  /-- The Gaussian martingale has covariance density `Db` on the horizon and is frozen after it (2026-10-15
  repair, ISSUES §I: `IsHilbertMartingaleWithCovariation` states the covariation martingale for all times, while
  `Db` is only constrained on `[0,T]`; without the truncation Lemma 3.29 was refutable). -/
  gaussian : ∀ S : ℝ, 0 ≤ S → ENNReal.ofReal S ≤ T →
    IsHilbertMartingaleWithCovariation (P' : Measure Ω') ℱ' S Gb
      (fun r _ => if ENNReal.ofReal r ≤ T then Db r else 0)
  /-- The difference `M∘π - Gb`, stopped at the horizon `S`, is a Hilbert martingale with covariation density
  `Sd` on `[0,S]` (2026-10-15 repair, ISSUES §I: unstopped, the all-time covariation identity of
  `IsHilbertMartingaleWithCovariation` hits Bochner junk values after `T`, where `Sg` is unconstrained; over all
  `S ≤ T` the stopped statements are exactly the source's martingale property on `[0,T]`). -/
  difference : ∀ S : ℝ, 0 ≤ S → ENNReal.ofReal S ≤ T →
    IsHilbertMartingaleWithCovariation (P' : Measure Ω') ℱ' S
      (fun τ ω' => M (min τ S) (π ω') - Gb (min τ S) ω') (fun r ω' => if r ≤ S then Sd r ω' else 0)
  indep : Indep (𝒢.1.comap π)
    (⨆ τ ∈ {τ : ℝ | 0 ≤ τ ∧ ENNReal.ofReal τ ≤ T}, MeasurableSpace.comap (Gb τ) inferInstance)
    (P' : Measure Ω')
  cost : ∀ᵐ ω' ∂(P' : Measure Ω'), ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal r ≤ T →
    rel (traceNormForm (Sd r ω')) (cost r (π ω'))

/-- The existence of such a coupling (`IsAdaptedGaussianCoupling` for some enlargement, `Ḡ`, `Sd`). -/
def AdaptedGaussianCoupling {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (T : ℝ≥0∞) (𝒢 : InitialSigma ℱ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ))
    (rel : ℝ → ℝ → Prop) (cost : ℝ → Ω → ℝ) : Prop :=
  ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω') (π : Ω' → Ω)
    (ℱ' : Filtration ℝ mΩ') (Gb : ℝ → Ω' → H) (Sd : ℝ → Ω' → (H →L[ℝ] H →L[ℝ] ℝ)),
    IsAdaptedGaussianCoupling P ℱ T 𝒢 M Sg Db rel cost P' π ℱ' Gb Sd

/-- Lemma 3.24 (`M:U:lem:transport-noise`, "Transport-plan coupling of empirical and continuum noise",
TeX M L2396-2405).  `H = H^{-γ}_0`, `b_{x,j} = -∂_jδ_x`.  The martingale `M` of covariance `C_N^t` (here
`covForm γ q (μ_N^t)`, `q = q_N`) can be coupled to a Gaussian martingale with deterministic covariance
`C̄_N^t = covForm γ q μ^t`, independently of the initial σ-field `𝒢`, so that the trace density of their difference is at
most `C q_N W_2(μ_N^t, μ^t)²` (`U:eq:transport-bracket`).  `C` depends only on `(d, γ)`.
The proof uses only that `x ↦ b_{x,j}` is Lipschitz into `H` ("It is enough …", L2398); this is the case for
`γ > d/2 + 2` (the map is `C¹` into `H` for `γ > d/2 + 1 + 1`, L2284-2286), the hypothesis `hγ` (`K = 1`).

Technical hypotheses: `X` an `ℱ`-adapted configuration process, `ρ^t` probability densities, `M` an `L²` Hilbert
martingale with this covariation (`IsHilbertMartingaleWithCovariation`, which includes `E∫‖C_N^t‖₁ dt < ∞`; true for
the particle noise since `‖C_N^t‖₁ ≤ C q_N`). -/
-- 2026-10-15 repair (ISSUES §I, Q14 counterexample): the deterministic covariance `r ↦ covForm γ q (ρ r)` is assumed
-- measurable (as `IsDetCovDensity.meas` in Lemma 3.29); without it a non-measurable `ρ` refutes the coupling.
theorem transport_noise_coupling (hd : 1 ≤ d) (γ : ℝ) (hγ : (d : ℝ) / 2 + 2 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (N : ℕ) (_ : 1 ≤ N) (q : ℝ) (_ : 0 ≤ q) (T : ℝ)
      (_ : 0 ≤ T) (X : ℝ → Ω → Config d N) (_ : ∀ r, Measurable[ℱ r] (X r)) (ρ : ℝ → Torus d → ℝ)
      (_ : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
      (_ : ∀ x y : NegSobolev d γ, Measurable fun r => covForm γ q (withDensityReal (ρ r)) x y)
      (M : ℝ → Ω → NegSobolev d γ)
      (_ : IsHilbertMartingaleWithCovariation P ℱ T M
        (fun r ω => covForm γ q (empirical (X r ω)))),
      AdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M
        (fun r ω => covForm γ q (empirical (X r ω)))
        (fun r => covForm γ q (withDensityReal (ρ r))) (· ≤ ·)
        (fun r ω => C * q *
          (torusWassersteinE 2 (empirical (X r ω)) (withDensityReal (ρ r))).toReal ^ 2) := by
  sorry

/-! ### The remark on higher Wasserstein orders, and Corollary 3.26 -/

/-- Remark (unnumbered, "Higher Wasserstein orders", `M:@remark:L2482`, TeX M L2482-2496), for a fixed `p ≥ 2`, in the setting of
Theorem 2.1 (gradient dynamics, positive density bound, `HRS.GeneralSetup.general_fluctuation`): the same whole-path
coupling gives
`W_p(Law Ξ_N, Law Y_N) ≤ C_{T,p}( A_N ε_{N,p} + σ_N ‖∫_0^T 𝓔_N^t dt‖_{L^p} + ‖(∫_0^T ‖C_N^t - C̄_N^t‖_{𝔖₁} dt)^{1/2}‖_{L^p} )`
(`U:eq:general-Wp`), and, with the positive density bound, the last term may instead be
`C √q_N ‖(∫_0^T W_2(μ_N^t, μ^t)² dt)^{1/2}‖_{L^p}`.  Both conclusions are in `ℝ≥0∞` with all the `L^p` norms as
`lintegral`s, so "whenever these quantities are finite" is automatic (the right side is `∞` otherwise) and no real
integral is a junk value; the constant depends on `(b, p)` only.  The explicit first-moment covariance errors of
Theorem 2.1 are the `p = 2` specialisation (not restated here).

Technical hypotheses: those of `general_fluctuation` minus the energy-moment finiteness (not needed in `ℝ≥0∞`).

Statement repair (ISSUES.md, entries "5.14 `criterion_comparison`…" and "N:thm:dynamic …"; final entry "Filtered strong solutions …"): the remark uses the same whole-path coupling and the same empirical-adjoint identity as Theorem 2.1 (`B:prop:duality-identity`, Lemma 3.7), which needs a Brownian filtration, so `X` is assumed a filtered strong solution (`IsFilteredSolution`), the strong-solution adaptedness of A.1 that `IsStrongSolution` (measurability only, ISSUES D1) does not record.

Statement repair 2026-10-16 (ISSUES "SPEC-C0"): the completion constant `C₀` of `o_N` must be taken large enough (TeX M L546-555, L2279-2299 "Increasing its constant once suffices"), so the conclusion is now stated for every `C₀ ≥ C₀min` (with `C₀min` independent of `C₀`) and the setups `Within { b with C₀ := C₀ }`; previously `C₀` was pinned to `b.C₀` with no lower bound. -/
theorem general_fluctuation_Wp (b : GeneralBounds d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      let ε : ℝ≥0∞ := (∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X₀ ω))
          (withDensityReal (S.ρ N 0)) - η₀ ω‖ₑ ^ p ∂P) ^ (1 / p)
      let En : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (S.energyCompletion N (X (Real.toNNReal t) ω) t)) ^ p ∂P) ^ (1 / p)
      let Cv : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (traceNormForm
            (covForm (S.γ : ℝ) q (empirical (X (Real.toNNReal t) ω)) -
              covForm (S.γ : ℝ) q (withDensityReal (S.ρ N t))))) ^ (p / 2) ∂P) ^ (1 / p)
      let Wt : ℝ≥0∞ := (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) S.T,
          torusWassersteinE 2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)) ^ 2)
            ^ (p / 2) ∂P) ^ (1 / p)
      wassersteinE p Ξ YN ≤
          ENNReal.ofReal C * (ENNReal.ofReal A * ε + ENNReal.ofReal σ * En + Cv) ∧
      wassersteinE p Ξ YN ≤
          ENNReal.ofReal C * (ENNReal.ofReal A * ε + ENNReal.ofReal σ * En +
            ENNReal.ofReal (Real.sqrt q) * Wt) := by
  sorry

/-- Corollary 3.26 (`M:U:cor:coefficients`, "Comparison with an `N`-independent linear limit", TeX M L2498-2511),
gradient case in the setting of Theorem 2.1.  `Y_N` solves the linear equation with the `N`-dependent coefficients
`(ν_N, q_N, ρ_N, A_N η°)` and `Y_∞` the one with the limiting coefficients `(ν_∞ = Dlim.invβ, q_∞, ρ_∞, A_∞ η°)`, both
in `E_{γ+2}`.  With `Δ_N := |ν_N - ν_∞| + |q_N - q_∞| + |A_N - A_∞| + sup_{t≤T} ‖ρ_N^t - ρ_∞^t‖_{C^{K}}` (the "scalar
discrepancies and a sufficiently high fixed coefficient norm discrepancy"), under the uniform coefficient bounds, the `W_1`
comparison of the two linear paths in `𝒳_{γ+2,T}` has the additional error
`C_T (1 + ‖η°‖_{L²(H^{-γ})}) (Δ_N + √Δ_N)` (`U:eq:coefficient-rate`); the `W_2` statement has the same extra term, and the
smooth metric `d_{C_b²}` is bounded by the same quantity (the `W_1` bound, `d_2 ≤ d_1 ≤ W_1`).  The bound is non-asymptotic
(convergence of the coefficients is not used: the TeX "Suppose … converge" only gives meaning to `Δ_N → 0`);
`‖η°‖_{L²}` is `eLpNorm η₀ 2 P ∈ ℝ≥0∞` (so no hypothesis `η° ∈ L²` is needed, the bound being trivial otherwise).

AMBIGUITY (L2502-2503): "a sufficiently high fixed coefficient norm" is not specified; the reading used is
`K = γ + 2d + 12`, the order of the uniform coefficient bounds of Theorem 2.1 (L538-546).
Technical hypotheses: the limiting coefficients satisfy the same uniform bounds as `S` (probability densities,
`(K, Λ)`-regular, `ρ_∞ ≥ c` and `ν_∞ ≤ B_β`), and `ρ_∞` is weakly continuous in time (the `cont` field of
`PDE.CoeffHyp`; the TeX's `ρ_∞` is the limit on `[0,T]` of the time-continuous `ρ_N`).  Repair 2026-10-16 (ISSUES §I
"3.26"): without it a time-discontinuous `ρ_∞` has no classical adjoint solution, `propagator` is the junk `0`,
`Y_∞` is forced to be `0`, and the bound fails for `Δ → 0`. -/
theorem coefficient_comparison (b : GeneralBounds d) :
    ∃ C : ℝ, 0 < C ∧ ∀ S : GeneralSetup d, S.Within b → S.MFHyp → S.PosDensityWith b.c →
      ∀ (Dlim : DynData d), Dlim.s = S.s → Dlim.M = -1 → Dlim.V = S.V → Dlim.invβ ≤ b.Bβ →
      ∀ (qlim Alim : ℝ), 0 ≤ qlim → ∀ ρlim : ℝ → Torus d → ℝ,
        (∀ t ∈ Set.Icc (0 : ℝ) S.T, IsProbDensity (ρlim t)) →
        IsRegularMF (S.γ + 2 * d + 12) S.Λ S.T ρlim → (∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ x, b.c ≤ ρlim t x) →
        (∀ ψ : Torus d → ℝ, Continuous ψ →
          ContinuousOn (fun r => ∫ x, ψ x * ρlim r x) (Set.Icc (0 : ℝ) S.T)) →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
        (Y Ylim : ℝ → Ω → NegSobolev d ((S.γ : ℝ) + 2)),
        IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) ((S.γ : ℝ) + 2)
          (qScale N (S.κ N) (S.invβ N)) S.T
          (fun ω => Ascale N (S.κ N) (S.invβ N) • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Y →
        IsLinearFluctuationSolution P Dlim ρlim ((S.γ : ℝ) + 2) qlim S.T
          (fun ω => Alim • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Ylim →
        let Δ : ℝ := |S.invβ N - Dlim.invβ| + |qScale N (S.κ N) (S.invβ N) - qlim| +
          |Ascale N (S.κ N) (S.invβ N) - Alim| +
          ⨆ t : Set.Icc (0 : ℝ) S.T, Torus.cbNorm (S.γ + 2 * d + 12) (fun x => S.ρ N t x - ρlim t x)
        let B : ℝ≥0∞ := ENNReal.ofReal C * (1 + eLpNorm η₀ 2 P) * ENNReal.ofReal (Δ + Real.sqrt Δ)
        let LN := law P (toPath ((S.γ : ℝ) + 2) S.T Y)
        let Llim := law P (toPath ((S.γ : ℝ) + 2) S.T Ylim)
        wassersteinE 1 LN Llim ≤ B ∧ wassersteinE 2 LN Llim ≤ B ∧
          ENNReal.ofReal (smoothDist 2 LN Llim) ≤ B := by
  sorry

/-! ### Proposition 3.28: smooth comparison and decaying history -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A strongly continuous deterministic evolution `V(t,r)` on `H`, `0 ≤ r ≤ t ≤ T` (cocycle, `V(t,t) = 1`,
strong continuity). -/
def IsPlainEvolution (V : ℝ → ℝ → H →L[ℝ] H) (T : ℝ) : Prop :=
  (∀ t ∈ Set.Icc (0 : ℝ) T, V t t = 1) ∧
  (∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → t ≤ T → (V t r).comp (V r s) = V t s) ∧
  ∀ x : H, ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2 x) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}

/-- The one-space maximal estimate `P:eq:maximal` for the evolution `V`, uniformly on windows `[a,a+T]`, `a ≥ 0`, with
constant `Cmax`: for every continuous `H`-valued martingale `M` with covariance density `C_u` and every continuous
stochastic convolution `Z_t = ∫_a^t V(t,u) dM_u` on `[a,a+T]` with each `Z_t` a.e. measurable,
`E sup_{a≤t≤a+T} ‖Z_t‖² ≤ Cmax E ∫_a^{a+T} Tr C_u du` (both sides in `ℝ≥0∞`).  The sample space ranges over `Type u`
(ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"; `u = 0` is the previous `Type`).
Statement repair (ISSUES.md, entry "MAXWINDOWS"): the clause `∀ t ∈ [a,a+T], AEMeasurable (Z t) P` was missing.  `IsStochConv` uses
lower integrals, which do not determine a non-measurable `Z t`, and without the clause the predicate is false for every `T > 0`. -/
def MaxWindows [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (V : ℝ → ℝ → H →L[ℝ] H) (T Cmax : ℝ) : Prop :=
  ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (a : ℝ), 0 ≤ a →
    ∀ (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)),
      IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg →
      ∀ Z : ℝ → Ω → H, (∀ t ∈ Set.Icc a (a + T), AEMeasurable (Z t) P) →
        (∀ t ∈ Set.Icc a (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) M a t (Z t)) →
        (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc a (a + T))) →
        ∫⁻ ω, (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω‖ₑ) ^ 2 ∂P ≤
          ENNReal.ofReal Cmax *
            ∫⁻ ω, (∫⁻ r in Set.Icc a (a + T), ENNReal.ofReal (traceNormForm (Sg r ω))) ∂P

end Abstract

/-- Proposition 3.28 (`M:P:prop:comparison`, "Smooth comparison and decaying history", TeX M L2603-2641), the smooth
assertion `P:eq:abstract-smooth`.  `V(t,r)` is a deterministic evolution on a real separable Hilbert space `H` with
`‖V(t,r)‖ ≤ K e^{-c(t-r)}` (`c ≥ 0`; `c = 0` is "bounded evolution suffices on a fixed horizon" and the finite-horizon
version `a = 0`), `X(t) = V(t,0)X₀ + ∫_0^t V(t,r) dM_r + R(t)` with `M` a continuous martingale with integrable trace-class
covariance density `C_r` (`Sg`), the convolution and `R` having continuous `H`-valued paths, the Gaussian convolution
`X̄(t) = V(t,0)X̄₀ + ∫V dG` of the deterministic density `C̄_r` (`Cb`; `G` a continuous martingale with deterministic
covariation) being continuous, and `X₀, X̄₀` coupled in the initial σ-field `ℱ_0` (in which `M` remains a martingale).
For a window `[a, a+T]` and `w_a(r) = e^{-c(a-r)_+}`:
`d_2(X^{a+·}, X̄^{a+·}) ≤ K e^{-ca} E‖X₀ - X̄₀‖ + E‖R‖_{C([a,a+T];H)} + ½K² E ∫_0^{a+T} w_a(r)² ‖C_r - C̄_r‖_{𝔖₁} dr`,
the supremum norm in both terms, as an inequality in `ℝ≥0∞` (all expectations `lintegral`s).  `d_2 = smoothDist 2` on
`C([0,T];H)` (`PathSp T H`) of the window processes (`windowPath a T`).  `a ≥ 0`, `T ≥ 0` arbitrary.
Technical: measurability of `Z t, Z̄ t, R t` (so path laws are push-forwards, not the junk measure `0`).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): the sample space `Ω` and the Hilbert space `H` are universe-polymorphic (`Type*`, previously `Type`), as for Lemmas 3.17/3.27 (ISSUES universe-defect entry); the source has no universe restriction and the statement is unchanged at `Type`. -/
theorem comparison_smooth (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (V : ℝ → ℝ → H →L[ℝ] H) (_ : IsPlainEvolution V (a + T))
    (_ : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
    (X₀ X₀' : Ω → H) (_ : Measurable[ℱ 0] X₀) (_ : Measurable[ℱ 0] X₀')
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (_ : IsHilbertMartingaleWithCovariation P ℱ (a + T) M Sg)
    (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (_ : IsDetCovDensity (a + T) Cb)
    (_ : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
    (Z Zb R : ℝ → Ω → H)
    (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
    (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
    (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
    (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
    (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
    (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
    (X Xb : ℝ → Ω → H)
    (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (X₀ ω) + Z t ω + R t ω)
    (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω) :
    ENNReal.ofReal (smoothDist 2 (law P (windowPath a T X)) (law P (windowPath a T Xb))) ≤
      ENNReal.ofReal (K * Real.exp (-c * a)) * ∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ∂P +
        ∫⁻ ω, ‖windowPath a T R ω‖ₑ ∂P +
        ENNReal.ofReal (K ^ 2 / 2) *
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
            ENNReal.ofReal (Real.exp (-c * max (a - r) 0) ^ 2 * traceNormForm (Sg r ω - Cb r))) ∂P := by
  sorry

/-- Proposition 3.28, the Wasserstein assertion `P:eq:abstract-Wp` (`p = 1, 2`), TeX M L2620-2641: in addition `M = ∫Φ dW`
for a (progressive here, "predictable" in the TeX) Hilbert-Schmidt integrand and a cylindrical Brownian motion `W` of the
filtration `ℱ` (which contains the initial coupling), and the one-space maximal estimate holds uniformly on windows
(`MaxWindows V T Cmax`).  Then
`W_p(X^{a+·}, X̄^{a+·}) ≤ C_T e^{-ca} ‖X₀ - X̄₀‖_{L^p(H)} + ‖R‖_{L^p(C([a,a+T];H))} +
  C_T (E ∫_0^{a+T} w_a(r)² ‖C_r - C̄_r‖_{𝔖₁} dr)^{1/2}`.
`C = C_T` depends on `(K, c, T, Cmax)` only (chosen before `a`, hence uniform in the window start).  In `ℝ≥0∞`, all norms as
`lintegral`s.  Same hypotheses and technical conditions as `comparison_smooth`; `hΦ` as in
`HRS.hilbert_polar_coupling` (the integrand is `L²` on every finite horizon).

Statement repair (ISSUES.md, entry "Statement sweep repairs (ADAPTSPEC3)"): `Ω : Type u` and `H : Type*` are universe-polymorphic (previously `Type`), as for Lemmas 3.17/3.27 (ISSUES universe-defect entry); the hypothesis `MaxWindows` quantifies over sample spaces in the same universe `u` as `Ω` (`MaxWindows.{u}`, the one-space maximal estimate for all probability spaces of that universe), so the statement is unchanged at `u = 0`. -/
theorem comparison_wasserstein (K c T Cmax : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c) (hT : 0 ≤ T) (p : ℝ)
    (hp : p = 1 ∨ p = 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
    ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ)
      (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
      [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
      (V : ℝ → ℝ → H →L[ℝ] H) (_ : IsPlainEvolution V (a + T))
      (_ : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖V t r‖ ≤ K * Real.exp (-c * (t - r)))
      (_ : MaxWindows.{u, _} V T Cmax)
      (X₀ X₀' : Ω → H) (_ : Measurable[ℱ 0] X₀) (_ : Measurable[ℱ 0] X₀')
      {κ : Type} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (_ : IsCylindricalBrownian P ℱ W)
      (Φ : ℝ → Ω → κ → H) (_ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' Φ)
      (M : ℝ → Ω → H) (_ : IsHilbertItoIntegral P ℱ W Φ M)
      (G : ℝ → Ω → H) (Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (_ : IsDetCovDensity (a + T) Cb)
      (_ : IsHilbertMartingaleWithCovariation P ℱ (a + T) G (fun r _ => Cb r))
      (Z Zb R : ℝ → Ω → H)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P V (ContinuousLinearMap.id ℝ H) M 0 t (Z t))
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P V (ContinuousLinearMap.id ℝ H) G 0 t (Zb t))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ᵐ ω ∂P, ContinuousOn (fun t => R t ω) (Set.Icc 0 (a + T)))
      (_ : ∀ t, Measurable (Z t)) (_ : ∀ t, Measurable (Zb t)) (_ : ∀ t, Measurable (R t))
      (X Xb : ℝ → Ω → H)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, X t ω = V t 0 (X₀ ω) + Z t ω + R t ω)
      (_ : ∀ t ∈ Set.Icc (0 : ℝ) (a + T), ∀ ω, Xb t ω = V t 0 (X₀' ω) + Zb t ω),
      wassersteinE p (law P (windowPath a T X)) (law P (windowPath a T Xb)) ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) * (∫⁻ ω, ‖X₀ ω - X₀' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, ‖windowPath a T R ω‖ₑ ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal C *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal
              (Real.exp (-c * max (a - r) 0) ^ 2 *
                traceNormForm (hsCovForm (Φ r ω) - Cb r))) ∂P) ^ (1 / 2 : ℝ) := by
  sorry

/-! ### Lemma 3.29: reference-relative covariance cost -/

section Relative

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

open Classical in
/-- The nonnegative square root `C^{1/2}` of a nonnegative bounded form (`IsSqrtOfForm`; unique when it exists;
the junk value `0` otherwise). -/
def formSqrt (C : H →L[ℝ] H →L[ℝ] ℝ) : H →L[ℝ] H :=
  if h : ∃ S : H →L[ℝ] H, IsSqrtOfForm S C then h.choose else 0

/-- The squared optimal Gaussian factor cost
`𝔟(C,D)² = Tr C + Tr D - 2‖D^{1/2}C^{1/2}‖_{𝔖₁}` (`R:eq:Bures-bound`, L2686), with `Tr = ‖·‖_{𝔖₁} = traceNormForm`
for nonnegative trace-class forms and `‖A‖_{𝔖₁}` the trace norm of the form `(x,y) ↦ ⟨A x, y⟩`. -/
def bures2 (C D : H →L[ℝ] H →L[ℝ] ℝ) : ℝ :=
  traceNormForm C + traceNormForm D -
    2 * traceNormForm ((innerSL ℝ).comp ((formSqrt D).comp (formSqrt C)))

/-- The reference-relative quadratic form `𝒬_D(Δ) = ∑_{i,j} |⟨Δ e_i, e_j⟩|²/(d_i + d_j)` (`R:eq:relative-form`,
L2685) along the eigenbasis `e` of `D` with eigenvalues `dd i`, in `ℝ≥0∞` (the TeX remarks that the form may be
infinite). -/
def relQuad {ι : Type*} (e : HilbertBasis ι ℝ H) (dd : ι → ℝ) (Δ : H →L[ℝ] H →L[ℝ] ℝ) : ℝ≥0∞ :=
  ∑' p : ι × ι, ENNReal.ofReal (Δ (e p.1) (e p.2) ^ 2 / (dd p.1 + dd p.2))

/-- Lemma 3.29 (`M:R:lem:relative-covariance`, "Reference-relative covariance cost", TeX M L2682-2695), the operator
part.  `D` is an injective positive trace-class operator with orthonormal eigenbasis `e_j` and eigenvalues `d_j > 0`
(`D e_j = d_j e_j`, as forms; the eigenbasis is a Hilbert basis so `D` is injective), and `C ≥ 0` trace class (arbitrary
nullspace).  Then `𝔟(C,D)² ≤ 2 𝒬_D(C - D)` (`R:eq:Bures-bound`; in `ℝ≥0∞`, so also if the form is infinite), and if
`D ≥ c D₀` with `D₀` a positive diagonal operator in its *own* eigenbasis `e₀` (`D₀ e⁰_j = d⁰_j e⁰_j`, `d⁰_j > 0`; L2716:
"eigenbasis of `D₀` for the comparison"), the right side is at most `2 c⁻¹ 𝒬_{D₀}(C - D)`, `𝒬_{D₀}` computed in `e₀`. -/
theorem relative_covariance_cost [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {ι : Type*} (e : HilbertBasis ι ℝ H) (dd : ι → ℝ) (hdd : ∀ i, 0 < dd i)
    (D C : H →L[ℝ] H →L[ℝ] ℝ) (hD : IsTraceClassCov D) (hDe : ∀ i y, D (e i) y = dd i * inner ℝ (e i) y)
    (hC : IsTraceClassCov C) :
    ENNReal.ofReal (bures2 C D) ≤ 2 * relQuad e dd (C - D) ∧
      ∀ (D₀ : H →L[ℝ] H →L[ℝ] ℝ) {ι₀ : Type*} (e₀ : HilbertBasis ι₀ ℝ H) (dd₀ : ι₀ → ℝ),
        (∀ i, 0 < dd₀ i) → (∀ i y, D₀ (e₀ i) y = dd₀ i * inner ℝ (e₀ i) y) → ∀ c : ℝ, 0 < c →
        (∀ x, c * D₀ x x ≤ D x x) →
        2 * relQuad e dd (C - D) ≤ 2 * ENNReal.ofReal c⁻¹ * relQuad e₀ dd₀ (C - D) := by
  sorry

/-- Lemma 3.29, the adapted construction (L2693-2695): for a predictable covariance `C_t` (`Sg`) of an existing Hilbert
martingale `M` and a deterministic covariance density `D_t` (`Db`, `IsDetCovDensity`), there is an extension of the
probability space carrying a Gaussian martingale of covariance `D_t dt`, independent of the initial σ-field `𝒢`, such that
the difference martingale has trace density exactly `𝔟(C_t, D_t)²` (`AdaptedGaussianCoupling` with `rel = (· = ·)`),
whence `R:eq:Bures-bound` gives an adapted coupling of the entire martingales.  (Predictable is `ℱ`-adapted with
measurable entries, `IsHilbertMartingaleWithCovariation.sigma_adapted`, as in ISSUES §G.1.) -/
theorem relative_covariance_coupling {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T) (𝒢 : InitialSigma ℱ) (M : ℝ → Ω → H)
    (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (Db : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hDb : IsDetCovDensity T Db) :
    AdaptedGaussianCoupling P ℱ (ENNReal.ofReal T) 𝒢 M Sg Db (· = ·)
      (fun r ω => bures2 (Sg r ω) (Db r)) := by
  sorry

end Relative

/-! ### Lemma 3.30: the empirical current on one chart -/

/-- The feature space `ℓ²(ℤ^d)` carrying `b(u) = (√d_j e_j(u))_j`. -/
abbrev FeatureSpace (d : ℕ) := lp (fun _ : Lattice d => ℝ) 2

/-- The real orthonormal trigonometric basis of the unit cube with opposite faces identified, `ℤ^d`-indexed:
`e_0 = 1`, `e_k = √2 cos/sin(2π k·u)` (`Torus.realMode`), `‖e_k‖_∞ ≤ √2`. -/
def chartBasis (k : Lattice d) (u : Torus d) : ℝ :=
  if h : k = 0 then 1 else Torus.realMode ⟨k, h⟩ u

/-- `d_k = (1 + |k|²)^{-r}` (L2725-2726; the basis is indexed by its frequency `k`). -/
def chartWeight (r : ℕ) (k : Lattice d) : ℝ := (1 + Lattice.enorm k ^ 2) ^ (-(r : ℝ))

open Classical in
/-- The feature vector `b(u) = (√d_k e_k(u))_k ∈ ℓ²(ℤ^d)` (`0` if not square summable, which does not occur for
`r > d`: `∑_k (1+|k|²)^{-r} < ∞` iff `2r > d`). -/
def chartFeature (r : ℕ) (u : Torus d) : FeatureSpace d :=
  if h : Memℓp (fun k : Lattice d => Real.sqrt (chartWeight r k) * chartBasis k u) 2 then ⟨_, h⟩ else 0

/-- Lemma 3.30 (`M:R:lem:chart-current`, "Empirical current on one chart", TeX M L2731-2742).
Ambient space `X` with a deterministic reference measure `μ` and particles `x_i : Ω → X`, `μ_N = N⁻¹∑δ_{x_i}`.
A chart is `(U, ψ)`, `U ⊆ X` measurable, `ψ : X → 𝕋^d` (the unit cube with opposite faces identified) measurable; the
reference measure on the chart is `μ_U = (μ|_U) ∘ ψ⁻¹`, with density `h` relative to the unit-cube volume,
`cα ≤ h ≤ C_dens α` a.e. (`α > 0`); its empirical counterpart is `(μ_N|_U) ∘ ψ⁻¹`.  Assume `R:eq:linear-input` w.r.t. the
original reference measure `μ`: the one-particle marginal `m_N = E μ_N = N⁻¹∑ Law(x_i)` has density `g = dm_N/dμ`
with `m_N ≤ C_in μ` (`g ≤ C_in`) and `‖g - 1‖_{L²(μ)} ≤ C_in δ_N`, and `Var[μ_N(f)] ≤ C_in N⁻¹ ‖f‖²_{L²(μ)}` for
`f ∈ L²(μ)` (the variance as an `evariance`, in `ℝ≥0∞`, so that a non-`L²` statistic is not given the junk value `0`).
With `C_N = ∫ b⊗b dμ_N^{chart}`, `D = ∫ b⊗b dμ_U` (`outerCov`; `r > d`):
`E[𝔟(C_N, D)²] ≤ C (N⁻¹ + δ_N²)` (`R:eq:chart-error`), `C` independent of `α` and of the chart (it depends on
`d, r, c, C_dens, C_in`), and the same with both covariances multiplied by a fixed noise strength `κ > 0` (e.g. `2/β`),
at the price `κ` in the bound (`𝔟(κC,κD)² = κ 𝔟(C,D)²`).  `E` is a `lintegral` (in `ℝ≥0∞`).

Technical hypotheses: `X` a measurable space with `μ` finite; the particles measurable; test functions `f` measurable. -/
theorem chart_current (hd : 1 ≤ d) (r : ℕ) (hr : d < r) (c Cdens Cin : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
        (U : Set X) (_ : MeasurableSet U) (ψ : X → Torus d) (_ : Measurable ψ)
        (α : ℝ) (_ : 0 < α) (h : Torus d → ℝ)
        (_ : (μ.restrict U).map ψ = volume.withDensity fun u => ENNReal.ofReal (h u))
        (_ : ∀ᵐ u, c * α ≤ h u ∧ h u ≤ Cdens * α)
        (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : ℕ) (_ : 1 ≤ N) (xs : Fin N → Ω → X) (_ : ∀ i, Measurable (xs i)) (δ : ℝ)
        (g : X → ℝ) (_ : Measurable g)
        (_ : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
        (_ : ∀ᵐ x ∂μ, g x ≤ Cin)
        (_ : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
        (_ : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
          evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
            ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ)),
        (∫⁻ ω, ENNReal.ofReal (bures2
            (outerCov (chartFeature (d := d) r)
              ((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))
            (outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ))) ∂P ≤
          ENNReal.ofReal (C * ((N : ℝ)⁻¹ + δ ^ 2))) ∧
        ∀ κ : ℝ, 0 < κ →
          ∫⁻ ω, ENNReal.ofReal (bures2
            (κ • outerCov (chartFeature (d := d) r)
              ((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))
            (κ • outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ))) ∂P ≤
          ENNReal.ofReal (κ * (C * ((N : ℝ)⁻¹ + δ ^ 2))) := by
  sorry

end Uniform

end HRS
