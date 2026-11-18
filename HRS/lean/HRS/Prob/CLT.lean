import HRS.Prob.Metrics

/-!
# Quantitative martingale central limit theorems (finite-dimensional part)

Sources (HRS periodic main paper, Appendix A.4):
* Lemma A.19 `M:B:lem:dds` (source lines 10520-10526): scalar quantitative martingale CLT,
  `W_2(Law M_t, N(0,v)) ≤ (E|[M]_t - v|)^{1/2}`, with the Dambis–Dubins–Schwarz coupling.
* Lemma A.21 `M:B:lem:lindeberg` (10545-10551): multivariate quantitative martingale CLT
  in `d_{C²}`.
* The metric `d_{C²}` of `B:eq:dc2-def` (line 10042):
  `sup { ∫h dλ₁ - ∫h dλ₂ : h ∈ C²(E), ‖h‖_∞ + ‖Dh‖_∞ + ‖D²h‖_∞ ≤ 1 }`, which is `smoothDist 2`.

## Representation of quadratic variation (Mathlib has no stochastic calculus)

Mathlib (at the pinned version) has `Martingale` for general index sets, Brownian motion,
but no stochastic integral, no quadratic variation, no DDS theorem.  A continuous
square-integrable real martingale `M` and its quadratic variation `A = [M]` are therefore
represented *axiomatically through their characterising properties*: `M` is a continuous
martingale with `M_0 = 0`, `A` is continuous, adapted, nondecreasing with `A_0 = 0`, and
`M² - A` is a martingale.  (For continuous `L²` martingales this characterises `[M]`
uniquely; the uniqueness is standard and is part of package CLT-01.)  The vector case uses
the absolutely continuous covariation `[M^a,M^b]_τ = ∫_0^τ Σ^{ab}` with a given process
`Σ`.  This keeps the lemma statements exactly as in the source without building Itô
calculus first; when a stochastic-integral library exists (package SI-01), `IsQuadraticVariation`
is to be *proved* for `∫ Φ dW`, not assumed.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- `M` is a continuous square-integrable martingale on `[0,t]` with `M_0 = 0`, with respect
to the filtration `ℱ`. -/
structure IsContSqMartingale (ℱ : Filtration ℝ mΩ) (t : ℝ) (M : ℝ → Ω → ℝ) : Prop where
  martingale : Martingale M ℱ P
  zero : ∀ᵐ ω ∂P, M 0 ω = 0
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t)
  sq_int : ∀ τ ∈ Set.Icc 0 t, MemLp (M τ) 2 P

/-- `A` is the quadratic variation `[M]` of `M`: continuous, adapted, nondecreasing, `A_0 = 0`,
and `M² - A` is a martingale. -/
structure IsQuadraticVariation (ℱ : Filtration ℝ mΩ) (t : ℝ) (M A : ℝ → Ω → ℝ) : Prop where
  adapted : Adapted ℱ A
  zero : ∀ᵐ ω ∂P, A 0 ω = 0
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => A τ ω) (Set.Icc 0 t)
  mono : ∀ᵐ ω ∂P, MonotoneOn (fun τ => A τ ω) (Set.Icc 0 t)
  compensator : Martingale (fun τ ω => M τ ω ^ 2 - A τ ω) ℱ P

/-- The centered real Gaussian `N(0,v)` (`v ≥ 0`). -/
def gaussianLaw (v : ℝ) : Measure ℝ := ProbabilityTheory.gaussianReal 0 (Real.toNNReal v)

/-! Lemma A.19 `M:B:lem:dds` (`dds_wasserstein_bound`, `dds_coupling`) is stated in
`HRS/Prob/DDSCoupling.lean` (moved unchanged; the proof uses `HRS/Stochastic`). -/

/-! ### Multivariate version (Lemma A.21) -/

section Multivariate

variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The Euclidean matrix norm used as `‖·‖_{S_1}` on symmetric matrices: trace norm via the
variational formula `sup_{U orthogonal} tr(Qᵀ U)` (`traceNormMatrix`). -/
abbrev s1Norm (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ := traceNormMatrix Q

/-- `M` is a continuous `ℝ^p`-valued martingale on `[0,t]` with `M_0 = 0` and absolutely
continuous quadratic covariation `[M^a,M^b]_τ = ∫_0^τ Σ^{ab}_σ dσ`, `Σ_σ ≥ 0` symmetric
(source lines 10546-10547; the source presupposes that the Lebesgue integrals exist, which
`sigma_pathint` and `sigma_entry_int` record: without them the Bochner integrals below take the
junk value `0` on non-integrable paths), represented through: each pair `M^a M^b - ∫_0^· Σ^{ab}` is a
martingale, `Σ` is adapted and measurable in `(σ, ω)`. -/
structure IsVectorMartingaleWithCovariation (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ) : Prop where
  martingale : ∀ a : Fin p, Martingale (fun τ ω => M τ ω a) ℱ P
  zero : ∀ᵐ ω ∂P, M 0 ω = 0
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t)
  sq_int : ∀ τ ∈ Set.Icc 0 t, MemLp (M τ) 2 P
  sigma_meas : Measurable (Function.uncurry Sg)
  sigma_adapted : ∀ σ, Measurable[ℱ σ] (Sg σ)
  sigma_psd : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc 0 t, (Sg σ ω).PosSemidef
  sigma_int : Integrable (fun ω => ∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω)) P
  sigma_pathint : ∀ᵐ ω ∂P, IntegrableOn (fun σ => s1Norm (Sg σ ω)) (Set.Icc 0 t)
  sigma_entry_int : ∀ᵐ ω ∂P, ∀ a b : Fin p, IntegrableOn (fun σ => Sg σ ω a b) (Set.Icc 0 t)
  covariation : ∀ a b : Fin p,
    Martingale (fun τ ω => M τ ω a * M τ ω b - ∫ σ in Set.Icc 0 τ, Sg σ ω a b) ℱ P

/- `multivariate_martingale_clt` and `multivariate_martingale_clt_dc2` (Lemma A.21) are stated and
proved in `HRS/Prob/MartingaleCLT.lean` (that file imports `HRS.Prob.MartingaleLindeberg`, which
imports this one). -/

end Multivariate

end HRS
