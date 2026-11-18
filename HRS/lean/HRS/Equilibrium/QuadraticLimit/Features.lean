import HRS.Equilibrium.QuadraticLimit.Spectral
import HRS.Equilibrium.QuadraticLimit.FeaturesAux
import HRS.Equilibrium.QuadraticLimit.FeaturesAuxG
import HRS.Equilibrium.QuadraticLimit.FeaturesAuxC
import HRS.Equilibrium.QuadraticLimit.FeaturesAuxE

/-!
# Lemma 7.5 `quadratic_limit`: finite-rank product-law limits and the Gibbs tilt (packet Q08,
sub-packet `Features`)

Skeleton file (statements only, `sorry`-ed, all TRUE as written).

* `q08_gibbs_isProb`, `q08_measurable_energy`, `q08_integrable_energy`: the first conjunct of Lemma 7.5
  and the measure-theoretic bookkeeping for the laws of `(B_N, ζ_N)` under `Q_{N,β}`.
* `q08_weight_Lq`: `sup_N ‖dQ_N/dμ^{⊗N}‖_{L^q(μ^{⊗N})} < ∞` for every `q < ∞`
  (this is Prop 5.5 `perturbed_pressure`, with `θ = 0`, `β` replaced by `qβ`, `Nδ_N = 1` for `s < d/2`).
* `q08_energy_L2`: `L²(μ^{⊗N})` bound of the modulated energy of an `L²(μ⊗μ)` pair kernel, uniform in `N`
  (Hoeffding decomposition; `Var((1/N)∑_{i<j}k_c) = (N-1)/(2N) ‖k_c‖²`).
* `q08_clt_quadratic`: multivariate CLT for orthonormal centred `L²` coordinates, with convergence of
  integrals of continuous test functions of quadratic growth (Cramér-Wold + CLT in Mathlib, plus
  uniform integrability of `|S_N|²` since `E|S_N|² = L = E|G|²` for all `N`).
* `q08_gauss_tilt`: exact Gaussian tilt `N(0,I)` by `exp(-(β/2) sᵀAs)` is `N(0,(I+βA)^{-1})`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

variable {d : ℕ} (D : Q08Data d)

/-! ### Bookkeeping -/

/-- `Q_{N,β}(μ)` is a probability measure for `N ≥ 1` (positive finite normaliser). -/
theorem q08_gibbs_isProb (N : ℕ) (hN : 1 ≤ N) : IsProbabilityMeasure (D.Gibbs N) :=
  q08f_gibbs_isProb D N hN

/-- The modulated energy of the kernel `h` is a measurable function of the configuration. -/
theorem q08_measurable_energy (N : ℕ) :
    Measurable (fun X : Config d N => modulatedEnergy D.h X D.μ) := by
  haveI := q08_isProb_μ D
  exact measurable_modulatedEnergy (q08f_rowOK_h D)

/-- First conjunct of Lemma 7.5. -/
theorem q08_integrable_energy (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun X : Config d N => modulatedEnergy D.h X D.μ) (D.Gibbs N) :=
  q08f_integrable_energy D N hN

/-- Uniform `L^q` bound of the Gibbs density with respect to the product law. -/
theorem q08_weight_Lq (q : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∫⁻ X, ((D.Gibbs N).rnDeriv (D.prodLaw N) X) ^ q ∂(D.prodLaw N) ≤ ENNReal.ofReal C :=
  q08f_weight_Lq D q hq

/-! ### `L²` bound of the energy of a pair kernel under the product law -/

/-- For a symmetric measurable kernel `k ∈ L²(μ⊗μ)` and a probability measure `μ`:
`E_{μ^{⊗N}} (N F_N^k + ½ ∬ k)² ≤ 3 ∬ k²` for all `N ≥ 1` (here `E_{μ^{⊗N}} N F_N^k = -½ ∬ k`). -/
theorem q08_energy_L2 (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (k : Torus d → Torus d → ℝ) (hm : Measurable (Function.uncurry k)) (hs : ∀ x y, k x y = k y x)
    (hk : Integrable (fun z : Torus d × Torus d => k z.1 z.2 ^ 2) (μ.prod μ))
    (N : ℕ) (hN : 1 ≤ N) :
    ∫ X : Config d N, ((N : ℝ) * modulatedEnergy k X μ + (1 / 2) * ∫ x, ∫ y, k x y ∂μ ∂μ) ^ 2
        ∂(Measure.pi fun _ => μ) ≤ 3 * ∫ x, ∫ y, k x y ^ 2 ∂μ ∂μ := by
  have h := q08e_main μ k hm hk hs hN
  rw [integral_prod (fun z : Torus d × Torus d => k z.1 z.2 ^ 2) hk] at h
  exact h

/-! ### Finite-rank CLT -/

/-- Multivariate CLT in `ℝ^L` for an orthonormal family of centred `L²(μ)` functions, with convergence
of the integrals of continuous test functions of quadratic growth:
`S_N = N^{-1/2} (∑_k u_i(X_k))_{i<L}` under `μ^{⊗N}` converges to `N(0, I_L)`. -/
theorem q08_clt_quadratic (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (L : ℕ)
    (u : Fin L → Torus d → ℝ) (hm : ∀ i, Measurable (u i)) (h2 : ∀ i, MemLp (u i) 2 μ)
    (h0 : ∀ i, ∫ x, u i x ∂μ = 0)
    (ho : ∀ i j, ∫ x, u i x * u j x ∂μ = if i = j then 1 else 0)
    (Ψ : EuclideanSpace ℝ (Fin L) → ℝ) (hΨ : Continuous Ψ) (C₀ : ℝ)
    (hgr : ∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) :
    Tendsto (fun N : ℕ => ∫ X : Config d N,
        Ψ (WithLp.toLp 2 fun i : Fin L => (Real.sqrt N)⁻¹ * ∑ k : Fin N, u i (X k))
          ∂(Measure.pi fun _ => μ)) atTop
      (𝓝 (∫ s, Ψ s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L))
        (1 : Matrix (Fin L) (Fin L) ℝ)))) :=
  q08c_clt μ u hm h2 h0 ho Ψ hΨ C₀ hgr

/-! ### Gaussian tilt -/

/-- Tilting the standard Gaussian of `ℝ^L` by `exp(-(β/2) sᵀAs)` (`A ≥ 0`, `β ≥ 0`) gives the Gaussian
with covariance `M = (I + βA)^{-1}`: for bounded measurable `f`,
`∫ f e^{-(β/2) sᵀAs} dγ = (∫ e^{-(β/2) sᵀAs} dγ) ∫ f dN(0,M)`. -/
theorem q08_gauss_tilt {L : ℕ} (A M : Matrix (Fin L) (Fin L) ℝ) (hA : A.PosSemidef) (β : ℝ)
    (hβ : 0 ≤ β) (hM : M * (1 + β • A) = 1) (f : EuclideanSpace ℝ (Fin L) → ℝ)
    (hf : Measurable f) (hfb : ∃ K, ∀ s, |f s| ≤ K) :
    ∫ s, f s * Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ)) =
      (∫ s, Real.exp (-(β / 2) * ∑ i, ∑ j, A i j * s i * s j)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) (1 : Matrix (Fin L) (Fin L) ℝ))) *
        ∫ s, f s ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin L)) M) :=
  q08g_tilt A M hA β hβ hM f hf

end HRS.Q08

end
