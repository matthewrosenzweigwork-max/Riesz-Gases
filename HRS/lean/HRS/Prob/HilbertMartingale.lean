import HRS.Prob.MartingaleCLT
import HRS.Prob.HilbertCLT
import HRS.Stochastic.QuadraticVariation
import HRS.Stochastic.DDSCore

/-!
# Hilbert-space martingale CLT layer (package CLT-02)

Source (HRS periodic main paper, Appendix A.4 and Section 3):
* Remark 3.8 `M:B:rem:multitime` (source lines 1705-1707): joint statistics at several times
  through a single vector martingale with integrands extended by zero.
* Remark A.20 `M:B:rem:conditional-coupling` (10536-10539): the DDS coupling given an initial
  sigma-field.
* Lemma A.22 `M:B:lem:hilbert-martingale-clt` (10600-10611): Hilbert-valued quantitative
  martingale CLT in `d_{C²}`, with its conditional form.
* Corollary A.23 `M:B:lem:hilbert-martingale-w2` (10629-10654): predictable polar coupling
  and the `W₂` bound.
* Corollary A.24 `M:B:cor:hilbert-wasserstein-assembly` (10672-10692): adding the initial
  term and the remainder.
* Remark A.25 `M:B:rem:clt-complex` (10698-10700): complex and multi-time statistics.
* Lemma A.27 `M:B:newprob:conditional-heat` (10788-10817): conditional Gaussian interpolation.
* Corollary A.28 `M:B:newprob:conditional-martingale` (10888-10900): retention of the initial
  fluctuation law.
* Lemma A.29 `M:B:newprob:initial-martingale` (10908-10931): initial sum and adapted martingale.
* Corollary A.30 `M:B:newprob:iid` (10978-10994): independent initial sampling.
* Remark A.32 `M:B:newprob:several-times` (11037-11055): several observation times.

## Representation decisions (recorded in `docs/ISSUES.md` §B, CLT-02)

* **Hilbert-valued martingales with covariation.** Mathlib has no Hilbert-valued stochastic
  calculus.  As for `IsVectorMartingaleWithCovariation` (ISSUES §B C1), an `H`-valued continuous
  square-integrable martingale with predictable tensor quadratic variation
  `⟨⟨M⟩⟩_t = ∫_0^t Σ_r dr` is represented by its characterising properties
  (`IsHilbertMartingaleWithCovariation`): every coordinate `⟨M, x⟩` is a martingale, and
  `⟨M,x⟩⟨M,y⟩ - ∫_0^· Σ_r(x,y) dr` is a martingale for all `x, y ∈ H`.  `Σ_r` is a bounded
  bilinear form (`H →L[ℝ] H →L[ℝ] ℝ`, the form of the operator), nonnegative and trace class
  in the sense of `IsTraceClassCov` (`HRS/Prob/HilbertCLT.lean`).
* **Trace norm.** `‖C‖_{𝔖₁}` of a bounded bilinear form is defined by the variational formula
  `sup ∑_i |C(e_i, f_i)|` over finite orthonormal families `(e_i)`, `(f_i)` (`traceNormForm`);
  for trace-class forms this is the Schatten-1 norm and the real supremum is attained on a
  bounded set, so no junk value arises in the statements (all `Σ_r`, `Σ̄_r` are assumed trace
  class, as in the source).  Measurability of `ω ↦ traceNormForm (Σ_r ω - Σ̄_r)` follows from
  separability of `H` (countable dense set of orthonormal families); it is a lemma, not a
  hypothesis.
* **Cylindrical Brownian motions and Hilbert–Schmidt integrands.** A `U`-cylindrical Brownian
  motion is represented, through a Hilbert basis `(u_k)_{k ∈ κ}` of the separable space `U`
  (`κ` countable), by a family of independent real Brownian motions
  `W : ℝ≥0 → Ω → κ → ℝ`, every finite subfamily being an `IsBrownianFiltration`
  (`IsCylindricalBrownian`).  An integrand `Φ_r ∈ 𝓛₂(U,H)` is the family `Φ r ω k = Φ_r u_k`
  with `∑_k ‖Φ_r u_k‖² < ∞` (`IsHSIntegrand`; progressive measurability is used where the source
  says predictable, since the stochastic library is built on progressive integrands and the
  statements hold in that generality).  The `H`-valued integral `∫Φ dW` is characterised
  coordinatewise through the real Itô integrals of `HRS/Stochastic/Integral.lean`
  (`IsHilbertItoIntegral`), and `Σ_r = Φ_rΦ_r^*` is the form `hsCovForm (Φ r ω)`.
* **Operator square roots.** `Σ_r^{1/2}` is characterised, not constructed: `IsSqrtOfForm S C`
  says `S` is self-adjoint, nonnegative, and `⟨S x, S y⟩ = C x y`; this determines the
  nonnegative square root uniquely.
* **Enlargements.** "On an enlargement of the probability space" is a probability space `Ω'`
  with a measure-preserving map `π : Ω' → Ω` and a filtration `ℱ'` containing the pull-back of
  `ℱ`; all random variables of the original space are pulled back along `π`.  This keeps the joint
  realisation needed in Corollary A.24 (a copy in law, as in `dds_coupling`, would not).
* **The metric `d₃`** of `B:newprob:metric` (10763-10773) uses the MAX over the orders
  `1 ≤ j ≤ 3` of `sup ‖D^j h‖_op` (no bound on `‖h‖_∞` beyond boundedness); it is *not*
  `smoothDist 3` (SUM over the orders `0..3`).  It is defined here in `ℝ≥0∞` (`d3DistE`) so that
  it is `∞`, not a junk `0`, when the supremum is unbounded.
* **Lemma A.27's "local martingale with `E ∫ tr Σ < ∞`"** is, as its proof notes (10822-10823),
  a square-integrable martingale, and it is represented by `IsVectorMartingaleWithCovariation`
  (which asserts the martingale property); the hypotheses are equivalent.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

/-! ### Trace norm of a bilinear form and operator square roots -/

section TraceNorm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Finite orthonormal pairs of families in `H`: the index set of the variational formula for the
trace norm. -/
def OrthonormalPairs (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Type _ :=
  {p : (n : ℕ) × (Fin n → H) × (Fin n → H) // Orthonormal ℝ p.2.1 ∧ Orthonormal ℝ p.2.2}

/-- The trace (Schatten-1) norm `‖C‖_{𝔖₁}` of a bounded bilinear form on `H`, by the variational
formula `sup { ∑_i |C(e_i, f_i)| : (e_i), (f_i) finite orthonormal families }` (equal to
`tr √(C^*C)` for trace-class `C`; the real supremum is genuine when the set is bounded, which is
the case for every trace-class form and in particular for every difference of two forms
satisfying `IsTraceClassCov`). -/
def traceNormForm (C : H →L[ℝ] H →L[ℝ] ℝ) : ℝ :=
  ⨆ p : OrthonormalPairs H, ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|

/-- The trace `∑_i C(e_i,e_i)` of a form along a Hilbert basis (for nonnegative trace-class
forms this is `‖C‖_{𝔖₁}`, independently of the basis). -/
def traceAlong {ι : Type*} (b : HilbertBasis ι ℝ H) (C : H →L[ℝ] H →L[ℝ] ℝ) : ℝ :=
  ∑' i, C (b i) (b i)

/-- `S = C^{1/2}`: `S` is a self-adjoint nonnegative bounded operator with
`⟨S x, S y⟩ = C x y`, i.e. `S^*S = S² = C` as operators.  For a nonnegative bounded form `C`
this characterises the nonnegative square root uniquely. -/
structure IsSqrtOfForm (S : H →L[ℝ] H) (C : H →L[ℝ] H →L[ℝ] ℝ) : Prop where
  symm : ∀ x y, inner ℝ (S x) y = inner ℝ x (S y)
  nonneg : ∀ x, 0 ≤ inner ℝ (S x) x
  sq : ∀ x y, inner ℝ (S x) (S y) = C x y

/-- The covariance form `Σ = ΦΦ^*` of a Hilbert–Schmidt family `Φ = (Φ u_k)_k`:
`Σ(x,y) = ∑_k ⟨Φ u_k, x⟩ ⟨Φ u_k, y⟩` (as a sum in the Banach space of bilinear forms; it is
absolutely convergent when `∑_k ‖Φ u_k‖² < ∞`). -/
def hsCovForm {κ : Type*} (Φ : κ → H) : H →L[ℝ] H →L[ℝ] ℝ :=
  ∑' k, (innerSL ℝ (Φ k)).smulRight (innerSL ℝ (Φ k))

end TraceNorm

/-! ### Hilbert-valued martingales with absolutely continuous tensor covariation -/

section HilbertMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- An initial sigma-field `𝒢 ⊂ ℱ_0` (source line 10510: "we keep that initial sigma-field fixed
when constructing the independent Gaussian term").  Carried as a subtype so that `𝒢` does not
become a local `MeasurableSpace` instance shadowing the ambient one. -/
abbrev InitialSigma (ℱ : Filtration ℝ mΩ) : Type _ := {𝒢 : MeasurableSpace Ω // 𝒢 ≤ ℱ 0}

/-- A sub-σ-algebra of the ambient one, as a subtype (same reason as `InitialSigma`). -/
abbrev SubSigma (Ω : Type*) (mΩ : MeasurableSpace Ω) : Type _ := {𝒢 : MeasurableSpace Ω // 𝒢 ≤ mΩ}

/-- `M` is a continuous square-integrable `H`-valued martingale on `[0,t]` with `M_0 = 0` and
predictable tensor quadratic variation `⟨⟨M⟩⟩_τ = ∫_0^τ Σ_r dr`, `Σ_r` a nonnegative trace-class
form with `E ∫_0^t ‖Σ_r‖_{𝔖₁} dr < ∞` (Lemma A.22's hypotheses, source lines 10601-10605),
represented coordinatewise: for all `x, y ∈ H`, `⟨M,x⟩` and `⟨M,x⟩⟨M,y⟩ - ∫_0^· Σ_r(x,y) dr` are
martingales.  The integrability fields record that the Lebesgue integrals the source writes
exist (otherwise the Bochner integrals below would be junk `0`, ISSUES §E). -/
structure IsHilbertMartingaleWithCovariation (ℱ : Filtration ℝ mΩ) (t : ℝ)
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)) : Prop where
  martingale : ∀ x : H, Martingale (fun τ ω => inner ℝ (M τ ω) x) ℱ P
  zero : ∀ᵐ ω ∂P, M 0 ω = 0
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => M τ ω) (Set.Icc 0 t)
  sq_int : ∀ τ ∈ Set.Icc 0 t, MemLp (M τ) 2 P
  sigma_meas : ∀ x y : H, Measurable (Function.uncurry fun σ ω => Sg σ ω x y)
  sigma_adapted : ∀ σ, ∀ x y : H, Measurable[ℱ σ] (fun ω => Sg σ ω x y)
  sigma_traceClass : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc 0 t, IsTraceClassCov (Sg σ ω)
  sigma_int : Integrable (fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω)) P
  sigma_pathint : ∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (Sg σ ω)) (Set.Icc 0 t)
  sigma_entry_int : ∀ᵐ ω ∂P, ∀ x y : H, IntegrableOn (fun σ => Sg σ ω x y) (Set.Icc 0 t)
  covariation : ∀ x y : H,
    Martingale (fun τ ω => inner ℝ (M τ ω) x * inner ℝ (M τ ω) y -
      ∫ σ in Set.Icc 0 τ, Sg σ ω x y) ℱ P

/-- A deterministic covariance density `Σ̄ : [0,t] → 𝔖₁⁺(H)`: measurable (through its matrix
elements), nonnegative trace class, and integrable in trace norm (Lemma A.22, line 10606;
Corollary A.23, line 10638-10639 "strongly measurable with `∫_0^t Tr Σ̄_r dr < ∞`"). -/
structure IsDetCovDensity (t : ℝ) (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) : Prop where
  meas : ∀ x y : H, Measurable (fun σ => sb σ x y)
  traceClass : ∀ σ ∈ Set.Icc 0 t, IsTraceClassCov (sb σ)
  int : IntegrableOn (fun σ => traceNormForm (sb σ)) (Set.Icc 0 t)

/-- `γ` is the centered Gaussian law on `H` with covariance `∫_0^t Σ̄_r dr`. -/
def IsGaussianWithIntegratedCov (t : ℝ) (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (γ : Measure H) :
    Prop :=
  IsProbabilityMeasure γ ∧ IsCenteredGaussian γ ∧
    ∀ x y, covarianceBilin γ x y = ∫ σ in Set.Icc 0 t, sb σ x y

/-- The trace-norm discrepancy `E ∫_0^t ‖Σ_r - Σ̄_r‖_{𝔖₁} dr` (the right-hand sides of
`B:eq:hilbert-martingale-clt`, `B:eq:hilbert-martingale-w2` and the `D` of Corollary A.24). -/
def covDiscrepancy (t : ℝ) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) : ℝ :=
  ∫ ω, (∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ)) ∂P

/-! ### Route for Lemma A.22 (as formalised)

1. Reduce to finitely many coordinates: for an orthonormal family `b : Fin d → H` the coordinate
   process `⟨b_a, M⟩` is an `ℝ^d`-valued martingale with covariation matrix `(Σ(b_a,b_c))`
   (`isVectorMartingale_coord`); the compression of a trace-class form is contractive in the trace
   norm (`traceNormMatrix_compMat_le`, via the rank-one decomposition `exists_decomp'` and the
   bound `sum_abs_le_of_decomp`).
2. The law of the coordinates of `G` is `multivariateGaussian 0 (∫ Σ̄(b_a,b_c))` by uniqueness of
   Gaussian measures (`map_coord_gaussian`), and `multivariate_martingale_clt_dc2` gives the bound
   for `P_K M_t` and `P_K G` (`finite_dim_step`).
3. For test functions of the `d_{C²}` class (`cbUnitBall_comp_clm` transfers them to `ℝ^d`) the
   projection error is at most `E‖(I-P_K)M_t‖ + E‖(I-P_K)G‖`, which tends to `0` along the
   finite-dimensional subspaces `denseSub n` by dominated convergence (`hilbert_clt_core`).
   The measurability of `(σ,ω) ↦ ‖Σ-Σ̄‖_{𝔖₁}` uses a countable dense family of orthonormal pairs
   (`measurable_traceNormForm`), so that the Bochner integral `covDiscrepancy` is not a junk `0`
   (`discrepancy_integrable`).
4. The conditional statement is obtained from the unconditional one under `P[· | A]` for
   `A ∈ 𝒢 ⊂ ℱ_0` (`isHilbertMartingale_cond`: conditioning on a set of `ℱ_0` preserves the martingale
   fields), and then `ae_le_of_setIntegral_le_trim` on the `𝒢`-measurable functions
   `E[Φ(M_t) | 𝒢] - ∫Φ dγ` and `½ E[∫‖Σ-Σ̄‖ | 𝒢]`.  No finite-dimensional conditional Lindeberg
   estimate is needed. -/

/-! ### Helper lemmas for Lemma A.22 -/

section A22Aux

open HilbertCLTAux

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- A trace-class form is a sum of rank-one forms `∑_j ⟨ℓ_j,x⟩⟨ℓ_j,y⟩` with `∑ ‖ℓ_j‖² < ∞`. -/
lemma IsTraceClassCov.exists_decomp' [SecondCountableTopology H] {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : IsTraceClassCov C) :
    ∃ ℓ : ℕ → H, Summable (fun j => ‖ℓ j‖ ^ 2) ∧
      ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (C x y) := by
  obtain ⟨ι, b, htr⟩ := hC.trace
  have hA : IsPSDOp (formOp C) :=
    ⟨fun x y => by
      rw [inner_formOp, real_inner_comm, inner_formOp, hC.symm],
     fun x => by rw [inner_formOp]; exact hC.nonneg x⟩
  obtain ⟨ℓ, hs, hsum⟩ := exists_rank_one_decomp hA b
    (by simpa only [inner_formOp] using htr)
  exact ⟨ℓ, hs, fun x y => by simpa only [inner_formOp] using hsum x y⟩

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma sum_abs_le_of_decomp {C : H →L[ℝ] H →L[ℝ] ℝ} {ℓ : ℕ → H}
    (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    (hC : ∀ x y, HasSum (fun j => inner ℝ (ℓ j) x * inner ℝ (ℓ j) y) (C x y))
    {n : ℕ} (e f : Fin n → H) (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) :
    ∑ i, |C (e i) (f i)| ≤ ∑' j, ‖ℓ j‖ ^ 2 := by
  classical
  have hsm : ∀ i, Summable fun j => |inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i)| := by
    intro i
    refine Summable.of_nonneg_of_le (fun j => abs_nonneg _) (fun j => ?_)
      (hs.mul_right (‖e i‖ * ‖f i‖))
    rw [abs_mul]
    calc |inner ℝ (ℓ j) (e i)| * |inner ℝ (ℓ j) (f i)|
        ≤ (‖ℓ j‖ * ‖e i‖) * (‖ℓ j‖ * ‖f i‖) := by
          gcongr <;> exact abs_real_inner_le_norm _ _
      _ = ‖ℓ j‖ ^ 2 * (‖e i‖ * ‖f i‖) := by ring
  have h1 : ∀ i, |C (e i) (f i)| ≤ ∑' j, |inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i)| := by
    intro i
    rw [← (hC (e i) (f i)).tsum_eq]
    have := norm_tsum_le_tsum_norm (f := fun j => inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i))
      (by simpa [Real.norm_eq_abs] using hsm i)
    simpa [Real.norm_eq_abs] using this
  calc ∑ i, |C (e i) (f i)|
      ≤ ∑ i, ∑' j, |inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i)| :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = ∑' j, ∑ i, |inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i)| :=
        (Summable.tsum_finsetSum fun i _ => hsm i).symm
    _ ≤ ∑' j, ‖ℓ j‖ ^ 2 := by
      refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun i _ => hsm i) hs
      have hb1 := he.sum_inner_products_le (ℓ j) (s := Finset.univ)
      have hb2 := hf.sum_inner_products_le (ℓ j) (s := Finset.univ)
      have ha : ∀ x : H, ‖inner ℝ x (ℓ j)‖ ^ 2 = (inner ℝ (ℓ j) x) ^ 2 := by
        intro x; rw [real_inner_comm, Real.norm_eq_abs, sq_abs]
      simp only [ha] at hb1 hb2
      have : ∀ i, |inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i)| ≤
          (1 / 2) * ((inner ℝ (ℓ j) (e i)) ^ 2 + (inner ℝ (ℓ j) (f i)) ^ 2) := by
        intro i
        rw [abs_mul]
        nlinarith [sq_nonneg (|inner ℝ (ℓ j) (e i)| - |inner ℝ (ℓ j) (f i)|),
          sq_abs (inner ℝ (ℓ j) (e i)), sq_abs (inner ℝ (ℓ j) (f i))]
      calc ∑ i, |inner ℝ (ℓ j) (e i) * inner ℝ (ℓ j) (f i)|
          ≤ ∑ i, (1 / 2) * ((inner ℝ (ℓ j) (e i)) ^ 2 + (inner ℝ (ℓ j) (f i)) ^ 2) :=
            Finset.sum_le_sum fun i _ => this i
        _ = (1 / 2) * (∑ i, (inner ℝ (ℓ j) (e i)) ^ 2 + ∑ i, (inner ℝ (ℓ j) (f i)) ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ ‖ℓ j‖ ^ 2 := by linarith

end A22Aux

section A22Trace

open HilbertCLTAux

omit [MeasurableSpace H] [BorelSpace H] in
lemma bddAbove_pairSum {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) :
    BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|) := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  exact ⟨∑' j, ‖ℓ j‖ ^ 2, by
    rintro _ ⟨p, rfl⟩
    exact sum_abs_le_of_decomp hs hℓ _ _ p.2.1 p.2.2⟩

omit [MeasurableSpace H] [BorelSpace H] in
lemma bddAbove_pairSum_sub {C₁ C₂ : H →L[ℝ] H →L[ℝ] ℝ} (h₁ : IsTraceClassCov C₁)
    (h₂ : IsTraceClassCov C₂) :
    BddAbove (Set.range fun p : OrthonormalPairs H =>
      ∑ i, |(C₁ - C₂) (p.1.2.1 i) (p.1.2.2 i)|) := by
  obtain ⟨b₁, hb₁⟩ := bddAbove_pairSum h₁
  obtain ⟨b₂, hb₂⟩ := bddAbove_pairSum h₂
  refine ⟨b₁ + b₂, ?_⟩
  rintro _ ⟨p, rfl⟩
  have e1 := hb₁ ⟨p, rfl⟩
  have e2 := hb₂ ⟨p, rfl⟩
  simp only at e1 e2
  calc ∑ i, |(C₁ - C₂) (p.1.2.1 i) (p.1.2.2 i)|
      ≤ ∑ i, (|C₁ (p.1.2.1 i) (p.1.2.2 i)| + |C₂ (p.1.2.1 i) (p.1.2.2 i)|) :=
        Finset.sum_le_sum fun i _ => by
          simpa using abs_sub (C₁ (p.1.2.1 i) (p.1.2.2 i)) (C₂ (p.1.2.1 i) (p.1.2.2 i))
    _ = _ := Finset.sum_add_distrib
    _ ≤ b₁ + b₂ := by linarith

omit [MeasurableSpace H] [BorelSpace H] in
lemma pairSum_le_traceNormForm {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|))
    (p : OrthonormalPairs H) : ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)| ≤ traceNormForm C :=
  le_ciSup hb p

omit [MeasurableSpace H] [BorelSpace H] in
lemma traceNormForm_nonneg (C : H →L[ℝ] H →L[ℝ] ℝ) : 0 ≤ traceNormForm C :=
  Real.iSup_nonneg fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [MeasurableSpace H] [BorelSpace H] in
lemma traceNormForm_sub_le {C₁ C₂ : H →L[ℝ] H →L[ℝ] ℝ} (h₁ : IsTraceClassCov C₁)
    (h₂ : IsTraceClassCov C₂) :
    traceNormForm (C₁ - C₂) ≤ traceNormForm C₁ + traceNormForm C₂ := by
  refine Real.iSup_le (fun p => ?_) (add_nonneg (traceNormForm_nonneg _) (traceNormForm_nonneg _))
  have e1 := pairSum_le_traceNormForm (bddAbove_pairSum h₁) p
  have e2 := pairSum_le_traceNormForm (bddAbove_pairSum h₂) p
  calc ∑ i, |(C₁ - C₂) (p.1.2.1 i) (p.1.2.2 i)|
      ≤ ∑ i, (|C₁ (p.1.2.1 i) (p.1.2.2 i)| + |C₂ (p.1.2.1 i) (p.1.2.2 i)|) :=
        Finset.sum_le_sum fun i _ => by
          simpa using abs_sub (C₁ (p.1.2.1 i) (p.1.2.2 i)) (C₂ (p.1.2.1 i) (p.1.2.2 i))
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by linarith

/-- Compression of a bilinear form to an orthonormal family. -/
def compMat {d : ℕ} (b : Fin d → H) (C : H →L[ℝ] H →L[ℝ] ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a c => C (b a) (b c)

omit [MeasurableSpace H] [BorelSpace H] in
lemma traceNormMatrix_compMat_le {d : ℕ} {b : Fin d → H} (hb : Orthonormal ℝ b)
    {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hbdd : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)|)) :
    traceNormMatrix (compMat b C) ≤ traceNormForm C := by
  classical
  refine ciSup_le fun U => ?_
  set e : Fin d → H := fun a => ∑ c, (U : Matrix (Fin d) (Fin d) ℝ) c a • b c with he
  have hU : ∀ a a', ∑ c, (U : Matrix (Fin d) (Fin d) ℝ) c a * (U : Matrix (Fin d) (Fin d) ℝ) c a' =
      if a = a' then 1 else 0 := by
    intro a a'
    have h1 := Matrix.mem_unitaryGroup_iff'.1 U.2
    have := congrFun (congrFun h1 a) a'
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, star_trivial] at this
    exact this
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro a a'
    simp only [he, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    have : ∀ c c', inner ℝ (b c) (b c') = if c = c' then (1 : ℝ) else 0 := orthonormal_iff_ite.1 hb
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← hU a a']
    refine Finset.sum_congr rfl fun c _ => by ring
  have hpair : (⟨⟨d, e, b⟩, hon, hb⟩ : OrthonormalPairs H) ∈ Set.univ := trivial
  have h1 := pairSum_le_traceNormForm hbdd ⟨⟨d, e, b⟩, hon, hb⟩
  refine le_trans ?_ h1
  simp only
  have htr : Matrix.trace ((compMat b C).transpose * (U : Matrix (Fin d) (Fin d) ℝ)) =
      ∑ a, C (e a) (b a) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, compMat,
      Matrix.of_apply, he, map_sum, map_smul, sum_apply,
      smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
  rw [htr]
  exact Finset.sum_le_sum fun a _ => le_abs_self _

end A22Trace

section A22Meas

lemma iSup_dense_real {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    {D : Set X} (hD : Dense D) : ⨆ x, f x = ⨆ d : D, f d := by
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : IsEmpty D := ⟨fun d => hX.false d.1⟩
    simp
  have hDne : Nonempty D := by
    obtain ⟨d, hd⟩ := hD.nonempty
    exact ⟨⟨d, hd⟩⟩
  have key : ∀ s : ℝ, (∀ d : D, f d ≤ s) → ∀ x, f x ≤ s := by
    intro s hs x
    have hcl : IsClosed {x | f x ≤ s} := isClosed_le hf continuous_const
    have hsub : D ⊆ {x | f x ≤ s} := fun d hd => hs ⟨d, hd⟩
    have := closure_minimal hsub hcl
    rw [hD.closure_eq] at this
    exact this (Set.mem_univ x)
  by_cases hb : BddAbove (Set.range f)
  · apply le_antisymm
    · refine ciSup_le fun x => key _ (fun d => ?_) x
      exact le_ciSup (f := fun d : D => f d) ⟨hb.some, by rintro _ ⟨d, rfl⟩; exact hb.some_mem ⟨d, rfl⟩⟩ d
    · exact ciSup_le fun d => le_ciSup hb d.1
  · have hb' : ¬ BddAbove (Set.range fun d : D => f d) := by
      rintro ⟨B, hB⟩
      refine hb ⟨B, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact key B (fun d => hB ⟨d, rfl⟩) x
    rw [Real.iSup_of_not_bddAbove hb, Real.iSup_of_not_bddAbove hb']

omit [MeasurableSpace H] [BorelSpace H] in
lemma exists_countable_pairs :
    ∃ S : Set (OrthonormalPairs H), S.Countable ∧ ∀ C : H →L[ℝ] H →L[ℝ] ℝ,
      traceNormForm C = ⨆ s : S, ∑ i, |C (s.1.1.2.1 i) (s.1.1.2.2 i)| := by
  letI : TopologicalSpace (OrthonormalPairs H) :=
    inferInstanceAs (TopologicalSpace {p : (n : ℕ) × (Fin n → H) × (Fin n → H) //
      Orthonormal ℝ p.2.1 ∧ Orthonormal ℝ p.2.2})
  have : SecondCountableTopology (OrthonormalPairs H) :=
    (Topology.IsInducing.subtypeVal (Y := (n : ℕ) × (Fin n → H) × (Fin n → H))
      (t := {p | Orthonormal ℝ p.2.1 ∧ Orthonormal ℝ p.2.2})).secondCountableTopology
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (OrthonormalPairs H)
  refine ⟨S, hSc, fun C => ?_⟩
  have hcont : Continuous fun p : OrthonormalPairs H => ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)| := by
    have h1 : Continuous fun s : (n : ℕ) × (Fin n → H) × (Fin n → H) =>
        ∑ i : Fin s.1, |C (s.2.1 i) (s.2.2 i)| := by
      refine continuous_sigma fun n => ?_
      show Continuous fun a : (Fin n → H) × (Fin n → H) => ∑ i : Fin n, |C (a.1 i) (a.2 i)|
      fun_prop
    exact h1.comp continuous_subtype_val
  exact iSup_dense_real hcont hSd

omit [BorelSpace H] in
lemma measurable_traceNormForm {α : Type*} [MeasurableSpace α]
    (D : α → H →L[ℝ] H →L[ℝ] ℝ) (hD : ∀ x y : H, Measurable fun a => D a x y) :
    Measurable fun a => traceNormForm (D a) := by
  obtain ⟨S, hSc, hS⟩ := exists_countable_pairs (H := H)
  have : Countable S := hSc.to_subtype
  simp_rw [hS]
  refine Measurable.iSup fun s => ?_
  exact Finset.measurable_sum _ fun i _ => (hD _ _).abs

end A22Meas

section A22J

variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)}

lemma measurable_discrepancy_density (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (hsb : IsDetCovDensity t sb) :
    Measurable (Function.uncurry fun σ ω => traceNormForm (Sg σ ω - sb σ)) := by
  have := measurable_traceNormForm (H := H) (α := ℝ × Ω)
    (fun a => Sg a.1 a.2 - sb a.1) (fun x y => by
      simp only [ContinuousLinearMap.sub_apply]
      exact (hM.sigma_meas x y).sub ((hsb.meas x y).comp measurable_fst))
  exact this

lemma discrepancy_pathint (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (hsb : IsDetCovDensity t sb) :
    ∀ᵐ ω ∂P, IntegrableOn (fun σ => traceNormForm (Sg σ ω - sb σ)) (Set.Icc 0 t) ∧
      ∀ σ ∈ Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ) ≤
        traceNormForm (Sg σ ω) + traceNormForm (sb σ) := by
  have hmeas := measurable_discrepancy_density P hM hsb
  filter_upwards [hM.sigma_traceClass, hM.sigma_pathint] with ω hω hpath
  have hbd : ∀ σ ∈ Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ) ≤
      traceNormForm (Sg σ ω) + traceNormForm (sb σ) := fun σ hσ =>
    traceNormForm_sub_le (hω σ hσ) (hsb.traceClass σ hσ)
  refine ⟨?_, hbd⟩
  refine Integrable.mono' (hpath.add hsb.int)
    (hmeas.comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  exact hbd σ hσ

lemma discrepancy_integrable (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (hsb : IsDetCovDensity t sb) :
    Integrable (fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ)) P := by
  have hmeas := measurable_discrepancy_density P hM hsb
  have hsm : StronglyMeasurable fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ) := by
    have := (hmeas.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable
    exact this.integral_prod_right' (ν := volume.restrict (Set.Icc 0 t))
  set c : ℝ := ∫ σ in Set.Icc 0 t, traceNormForm (sb σ) with hc
  refine Integrable.mono' ((hM.sigma_int).add (integrable_const c)) hsm.aestronglyMeasurable ?_
  filter_upwards [discrepancy_pathint P hM hsb, hM.sigma_pathint] with ω hd hpath
  obtain ⟨hint1, hbd⟩ := hd
  rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _)]
  calc ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ)
      ≤ ∫ σ in Set.Icc 0 t, (traceNormForm (Sg σ ω) + traceNormForm (sb σ)) :=
        setIntegral_mono_on hint1 (hpath.add hsb.int) measurableSet_Icc hbd
    _ = (∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω)) + c := integral_add hpath hsb.int
    _ = _ := rfl

end A22J

section A22Comp

lemma cbUnitBall_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E →L[ℝ] F) (hg : ‖g‖ ≤ 1) {k : ℕ}
    {Φ : F → ℝ} (hΦ : Φ ∈ CbUnitBall F k) : (Φ ∘ g) ∈ CbUnitBall E k := by
  obtain ⟨h1, h2, h3⟩ := hΦ
  have hb : ∀ j ≤ k, ∀ x : E, ‖iteratedFDeriv ℝ j (Φ ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ j Φ (g x)‖ := by
    intro j hj x
    rw [g.iteratedFDeriv_comp_right h1 x (by exact_mod_cast hj)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have : ∏ _i : Fin j, ‖g‖ ≤ 1 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]; exact pow_le_one₀ (norm_nonneg _) hg
    calc _ ≤ ‖iteratedFDeriv ℝ j Φ (g x)‖ * 1 := by gcongr
      _ = _ := mul_one _
  refine ⟨h1.comp g.contDiff, fun j hj => ?_, ?_⟩
  · obtain ⟨B, hB⟩ := h2 j hj
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact (hb j hj x).trans (hB ⟨g x, rfl⟩)⟩
  · refine le_trans ?_ h3
    unfold cbNorm
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    obtain ⟨B, hB⟩ := h2 j hjk
    have : Nonempty E := ⟨0⟩
    refine ciSup_le fun x => (hb j hjk x).trans ?_
    exact le_ciSup (f := fun z : F => ‖iteratedFDeriv ℝ j Φ z‖) ⟨B, by rintro _ ⟨z, rfl⟩; exact hB ⟨z, rfl⟩⟩ (g x)

end A22Comp

section A22Coord

variable {d : ℕ}

/-- The coordinate map `x ↦ (⟨b_a, x⟩)_a ∈ ℝ^d`. -/
def hmCoordCLM (b : Fin d → H) : H →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a => innerSL ℝ (b a))

lemma hmCoordCLM_apply (b : Fin d → H) (x : H) (a : Fin d) :
    hmCoordCLM b x a = inner ℝ (b a) x := by
  simp [hmCoordCLM]

/-- The synthesis map `y ↦ ∑_a y_a b_a`. -/
def embedCLM (b : Fin d → H) : EuclideanSpace ℝ (Fin d) →L[ℝ] H :=
  ∑ a, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).smulRight (b a)

lemma embedCLM_apply (b : Fin d → H) (y : EuclideanSpace ℝ (Fin d)) :
    embedCLM b y = ∑ a, y a • b a := by
  simp [embedCLM]

lemma norm_embedCLM_apply {b : Fin d → H} (hb : Orthonormal ℝ b) (y : EuclideanSpace ℝ (Fin d)) :
    ‖embedCLM b y‖ = ‖y‖ := by
  have h1 : ‖embedCLM b y‖ ^ 2 = ∑ a, (y a) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, embedCLM_apply]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    have : ∀ c c', inner ℝ (b c) (b c') = if c = c' then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.1 hb
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => by ring
  have h2 : ‖y‖ ^ 2 = ∑ a, (y a) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have := h1.trans h2.symm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

lemma norm_embedCLM_le {b : Fin d → H} (hb : Orthonormal ℝ b) : ‖embedCLM b‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [norm_embedCLM_apply hb, one_mul]

end A22Coord

section A22Mat

lemma measurable_traceNormMatrix {α : Type*} [MeasurableSpace α] {d : ℕ}
    (D : α → Matrix (Fin d) (Fin d) ℝ) (hD : ∀ i j, Measurable fun a => D a i j) :
    Measurable fun a => traceNormMatrix (D a) := by
  have : SecondCountableTopology (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  have : SecondCountableTopology (Matrix.orthogonalGroup (Fin d) ℝ) :=
    (Topology.IsInducing.subtypeVal (Y := Matrix (Fin d) (Fin d) ℝ)
      (t := (Matrix.orthogonalGroup (Fin d) ℝ : Set (Matrix (Fin d) (Fin d) ℝ)))).secondCountableTopology
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Matrix.orthogonalGroup (Fin d) ℝ)
  have : Countable S := hSc.to_subtype
  have hcont : ∀ Q : Matrix (Fin d) (Fin d) ℝ, Continuous fun U : Matrix.orthogonalGroup (Fin d) ℝ =>
      Matrix.trace (Q.transpose * (U : Matrix (Fin d) (Fin d) ℝ)) := by
    intro Q
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul (continuous_subtype_val.matrix_elem j i)
  have heq : ∀ Q, traceNormMatrix Q = ⨆ s : S, Matrix.trace (Q.transpose * (s.1 : Matrix (Fin d) (Fin d) ℝ)) :=
    fun Q => iSup_dense_real (hcont Q) hSd
  simp_rw [heq]
  refine Measurable.iSup fun s => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => (hD j i).mul_const _

lemma posSemidef_gram {d : ℕ} {B : H →L[ℝ] H →L[ℝ] ℝ} (hsymm : ∀ x y, B x y = B y x)
    (hnn : ∀ x, 0 ≤ B x x) (b : Fin d → H) :
    (Matrix.of fun a c => B (b a) (b c) : Matrix (Fin d) (Fin d) ℝ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a c
    simp [Matrix.conjTranspose_apply, hsymm (b a) (b c)]
  · have : dotProduct (star x) (Matrix.mulVec (Matrix.of fun a c => B (b a) (b c)) x) =
        B (∑ a, x a • b a) (∑ c, x c • b c) := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, map_sum, map_smul,
        sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by
        rw [hsymm (b c) (b a)]; ring
    rw [this]
    exact hnn _

end A22Mat

section A22Vec

variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} {d : ℕ}

lemma isVectorMartingale_coord (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    {b : Fin d → H} (hb : Orthonormal ℝ b) :
    IsVectorMartingaleWithCovariation P ℱ t (fun τ ω => hmCoordCLM b (M τ ω))
      (fun σ ω => compMat b (Sg σ ω)) := by
  have hentry : ∀ (σ : ℝ) (ω : Ω) (a c : Fin d), compMat b (Sg σ ω) a c = Sg σ ω (b a) (b c) :=
    fun _ _ _ _ => rfl
  have hmeasS : Measurable (Function.uncurry fun σ ω => s1Norm (compMat b (Sg σ ω))) :=
    measurable_traceNormMatrix (fun a : ℝ × Ω => compMat b (Sg a.1 a.2))
      (fun i j => hM.sigma_meas (b i) (b j))
  have hbd : ∀ᵐ ω ∂P, ∀ σ ∈ Set.Icc 0 t,
      s1Norm (compMat b (Sg σ ω)) ≤ traceNormForm (Sg σ ω) := by
    filter_upwards [hM.sigma_traceClass] with ω h σ hσ
    exact traceNormMatrix_compMat_le hb (bddAbove_pairSum (h σ hσ))
  have hpath : ∀ᵐ ω ∂P, IntegrableOn (fun σ => s1Norm (compMat b (Sg σ ω))) (Set.Icc 0 t) := by
    filter_upwards [hbd, hM.sigma_pathint] with ω h1 h2
    refine Integrable.mono' h2
      (hmeasS.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_of_nonneg (traceNormMatrix_nonneg _)]
    exact h1 σ hσ
  refine
    { martingale := fun a => ?_
      zero := ?_
      cont := ?_
      sq_int := fun τ hτ => ?_
      sigma_meas := ?_
      sigma_adapted := fun σ => ?_
      sigma_psd := ?_
      sigma_int := ?_
      sigma_pathint := ?_
      sigma_entry_int := ?_
      covariation := fun a c => ?_ }
  · have h := hM.martingale (b a)
    have e : (fun τ ω => hmCoordCLM b (M τ ω) a) = fun τ ω => inner ℝ (M τ ω) (b a) := by
      funext τ ω; rw [hmCoordCLM_apply, real_inner_comm]
    show Martingale (fun τ ω => hmCoordCLM b (M τ ω) a) ℱ P
    rw [e]; exact h
  · filter_upwards [hM.zero] with ω h
    show hmCoordCLM b (M 0 ω) = 0
    rw [h, map_zero]
  · filter_upwards [hM.cont] with ω h
    exact (hmCoordCLM b).continuous.comp_continuousOn h
  · exact (hmCoordCLM b).comp_memLp' (hM.sq_int τ hτ)
  · refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => ?_
    exact hM.sigma_meas (b a) (b c)
  · letI : MeasurableSpace Ω := ℱ σ
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => ?_
    exact hM.sigma_adapted σ (b a) (b c)
  · filter_upwards [hM.sigma_traceClass] with ω h σ hσ
    exact posSemidef_gram (h σ hσ).symm (h σ hσ).nonneg b
  · have hsm : StronglyMeasurable fun ω => ∫ σ in Set.Icc 0 t, s1Norm (compMat b (Sg σ ω)) :=
      ((hmeasS.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable).integral_prod_right'
        (ν := volume.restrict (Set.Icc 0 t))
    refine Integrable.mono' hM.sigma_int hsm.aestronglyMeasurable ?_
    filter_upwards [hbd, hpath, hM.sigma_pathint] with ω h1 h2 h3
    rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Icc fun σ _ =>
      traceNormMatrix_nonneg _)]
    exact setIntegral_mono_on h2 h3 measurableSet_Icc h1
  · exact hpath
  · filter_upwards [hM.sigma_entry_int] with ω h a c
    exact h (b a) (b c)
  · have h := hM.covariation (b a) (b c)
    have e : (fun τ ω => hmCoordCLM b (M τ ω) a * hmCoordCLM b (M τ ω) c -
        ∫ σ in Set.Icc 0 τ, compMat b (Sg σ ω) a c) = fun τ ω =>
        inner ℝ (M τ ω) (b a) * inner ℝ (M τ ω) (b c) - ∫ σ in Set.Icc 0 τ, Sg σ ω (b a) (b c) := by
      funext τ ω; rw [hmCoordCLM_apply, hmCoordCLM_apply, real_inner_comm, real_inner_comm (M τ ω) (b c)]
      rfl
    show Martingale (fun τ ω => hmCoordCLM b (M τ ω) a * hmCoordCLM b (M τ ω) c -
        ∫ σ in Set.Icc 0 τ, compMat b (Sg σ ω) a c) ℱ P
    rw [e]; exact h

end A22Vec

section A22Gauss

variable {t : ℝ} {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} {d : ℕ}

lemma adjoint_hmCoordCLM (b : Fin d → H) (u : EuclideanSpace ℝ (Fin d)) :
    (hmCoordCLM b).adjoint u = embedCLM b u := by
  refine ext_inner_right ℝ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, embedCLM_apply, sum_inner]
  simp only [real_inner_smul_left, PiLp.inner_apply, hmCoordCLM_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [mul_comm]

lemma map_coord_gaussian {γ : Measure H} (hγ : IsGaussianWithIntegratedCov t sb γ)
    {b : Fin d → H} :
    γ.map (hmCoordCLM b) = ProbabilityTheory.multivariateGaussian 0
      (Matrix.of fun i j => ∫ σ in Set.Icc 0 t, sb σ (b i) (b j)) := by
  obtain ⟨hprob, hcg, hcov⟩ := hγ
  have hG : IsGaussian γ := hcg.1
  set S : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => ∫ σ in Set.Icc 0 t, sb σ (b i) (b j)
    with hSdef
  have hS : S = Matrix.of fun i j => covarianceBilin γ (b i) (b j) := by
    ext i j; simp [hSdef, hcov]
  have hSpsd : S.PosSemidef := by
    rw [hS]
    exact posSemidef_gram (B := covarianceBilin γ) (covarianceBilin_comm) (covarianceBilin_self_nonneg) b
  have hmem : MemLp id 2 γ := IsGaussian.memLp_two_id
  refine IsGaussian.ext ?_ ?_
  · rw [integral_id_multivariateGaussian']
    show ∫ x, x ∂(γ.map (hmCoordCLM b)) = 0
    rw [ContinuousLinearMap.integral_id_map (hmem.integrable (by simp))]
    have := HilbertCLTAux.gaussian_mean_zero (H := H) hcg
    have h0 : ∫ x, x ∂γ = 0 := this
    rw [h0, map_zero]
  · ext u v
    rw [covarianceBilin_multivariateGaussian hSpsd, covarianceBilin_map hmem, adjoint_hmCoordCLM,
      adjoint_hmCoordCLM, embedCLM_apply, embedCLM_apply]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, hS, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    ring

end A22Gauss

section A22FD

variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} {d : ℕ}

lemma finite_dim_step (ht : 0 ≤ t) (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (hsb : IsDetCovDensity t sb) {γ : Measure H} (hγ : IsGaussianWithIntegratedCov t sb γ)
    {b : Fin d → H} (hb : Orthonormal ℝ b) {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    |∫ ω, Φ (embedCLM b (hmCoordCLM b (M t ω))) ∂P -
        ∫ x, Φ (embedCLM b (hmCoordCLM b x)) ∂γ| ≤ (1 / 2) * covDiscrepancy P t Sg sb := by
  have hprob : IsProbabilityMeasure γ := hγ.1
  have hMc := isVectorMartingale_coord P hM hb
  have hsbmeas : Measurable (fun σ => compMat b (sb σ)) :=
    measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun c => hsb.meas (b a) (b c)
  have hsbmeasS : Measurable fun σ => s1Norm (compMat b (sb σ)) :=
    measurable_traceNormMatrix (fun σ => compMat b (sb σ)) (fun i j => hsb.meas (b i) (b j))
  have hsbint : IntegrableOn (fun σ => s1Norm (compMat b (sb σ))) (Set.Icc 0 t) := by
    refine Integrable.mono' hsb.int hsbmeasS.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_of_nonneg (traceNormMatrix_nonneg _)]
    exact traceNormMatrix_compMat_le hb (bddAbove_pairSum (hsb.traceClass σ hσ))
  have hsbpsd : ∀ σ ∈ Set.Icc 0 t, (compMat b (sb σ)).PosSemidef := fun σ hσ =>
    posSemidef_gram (hsb.traceClass σ hσ).symm (hsb.traceClass σ hσ).nonneg b
  have hdc2 := multivariate_martingale_clt_dc2 P ℱ t ht _ _ hMc (fun σ => compMat b (sb σ))
    hsbmeas hsbint hsbpsd
  have hgauss := map_coord_gaussian (b := b) hγ
  have hΦ' : (Φ ∘ embedCLM b) ∈ CbUnitBall (EuclideanSpace ℝ (Fin d)) 2 :=
    cbUnitBall_comp_clm _ (norm_embedCLM_le hb) hΦ
  have hmt : AEMeasurable (fun ω => hmCoordCLM b (M t ω)) P :=
    ((hmCoordCLM b).continuous.measurable.comp_aemeasurable
      (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable)
  have hlaw := abs_integral_sub_le_smoothDist hΦ' (law P fun ω => hmCoordCLM b (M t ω))
    (γ.map (hmCoordCLM b))
  have hc1 : ∫ z, (Φ ∘ embedCLM b) z ∂(law P fun ω => hmCoordCLM b (M t ω)) =
      ∫ ω, Φ (embedCLM b (hmCoordCLM b (M t ω))) ∂P :=
    integral_map hmt (hΦ.1.continuous.comp (embedCLM b).continuous).aestronglyMeasurable
  have hc2 : ∫ z, (Φ ∘ embedCLM b) z ∂(γ.map (hmCoordCLM b)) =
      ∫ x, Φ (embedCLM b (hmCoordCLM b x)) ∂γ :=
    integral_map (hmCoordCLM b).continuous.measurable.aemeasurable
      (hΦ.1.continuous.comp (embedCLM b).continuous).aestronglyMeasurable
  rw [hc1, hc2] at hlaw
  rw [hgauss] at hlaw
  refine hlaw.trans (le_trans hdc2 ?_)
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  unfold covDiscrepancy
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _)
    (discrepancy_integrable P hM hsb) ?_
  filter_upwards [discrepancy_pathint P hM hsb, hM.sigma_traceClass] with ω hd htc
  refine integral_mono_of_nonneg ((ae_restrict_iff' measurableSet_Icc).2
    (Filter.Eventually.of_forall fun σ _ => traceNormMatrix_nonneg _)) hd.1 ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  have : compMat b (Sg σ ω) - compMat b (sb σ) = compMat b (Sg σ ω - sb σ) := by
    ext a c; rfl
  show s1Norm (compMat b (Sg σ ω) - compMat b (sb σ)) ≤ traceNormForm (Sg σ ω - sb σ)
  rw [this]
  exact traceNormMatrix_compMat_le hb (bddAbove_pairSum_sub (htc σ hσ) (hsb.traceClass σ hσ))

end A22FD

section A22Tail

lemma exists_orthonormal_proj (K : Submodule ℝ H) [FiniteDimensional ℝ K] :
    ∃ (d : ℕ) (b : Fin d → H), Orthonormal ℝ b ∧
      ∀ x, embedCLM b (hmCoordCLM b x) = K.starProjection x := by
  classical
  let B := stdOrthonormalBasis ℝ K
  refine ⟨Module.finrank ℝ K, fun a => (B a : H), ?_, fun x => ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    have := orthonormal_iff_ite.1 B.orthonormal i j
    simpa using this
  · rw [embedCLM_apply, Submodule.starProjection_apply, B.orthogonalProjectionOnto_apply_eq_sum]
    simp [hmCoordCLM_apply]

lemma hm_tail_bound (ρ : Measure H) [IsProbabilityMeasure ρ] (hρ : MemLp id 2 ρ)
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    Integrable (fun x : H => ‖x - K.starProjection x‖) ρ ∧
    ∫ x, ‖x - K.starProjection x‖ ∂ρ ≤ Real.sqrt (∫ x, ‖x - K.starProjection x‖ ^ 2 ∂ρ) := by
  set A : H →L[ℝ] H := ContinuousLinearMap.id ℝ H - K.starProjection with hA
  have hAx : ∀ x, A x = x - K.starProjection x := fun x => by simp [hA]
  have hMem : MemLp (fun x : H => ‖x - K.starProjection x‖) 2 ρ := by
    have := (A.comp_memLp' hρ).norm
    simpa [hAx] using this
  exact ⟨hMem.integrable (by norm_num), integral_le_sqrt ρ hMem⟩

end A22Tail

section A22Main

variable {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
  {sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)}

lemma hilbert_clt_core (ht : 0 ≤ t) (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (hsb : IsDetCovDensity t sb) {γ : Measure H} (hγ : IsGaussianWithIntegratedCov t sb γ)
    {Φ : H → ℝ} (hΦ : Φ ∈ CbUnitBall H 2) :
    |∫ ω, Φ (M t ω) ∂P - ∫ x, Φ x ∂γ| ≤ (1 / 2) * covDiscrepancy P t Sg sb := by
  have hprob : IsProbabilityMeasure γ := hγ.1
  have hGm : MemLp id 2 γ := by
    have := hγ.2.1.1
    exact IsGaussian.memLp_two_id
  have hmt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hρ : MemLp id 2 (law P (M t)) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hmt]
    exact hM.sq_int t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure (law P (M t)) := inferInstance
  have hΦ1 : Φ ∈ CbUnitBall H 1 := cbUnitBall_anti (by norm_num) hΦ
  have hlip : LipschitzWith 1 Φ := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [dist_eq_norm, Real.dist_eq] using norm_sub_le_of_mem_one hΦ1 x y
  have hC : ∀ x y, dist (Φ x) (Φ y) ≤ 2 := fun x y => by
    rw [Real.dist_eq]
    have h1 := abs_apply_le_of_mem hΦ x
    have h2 := abs_apply_le_of_mem hΦ y
    calc |Φ x - Φ y| ≤ |Φ x| + |Φ y| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hΦc : Continuous Φ := hΦ.1.continuous
  set J := covDiscrepancy P t Sg sb with hJ
  have hρsq := HilbertCLTAux.integrable_sq_norm_of_memLp2 hρ
  have hγsq := HilbertCLTAux.integrable_sq_norm_of_memLp2 hGm
  have key : ∀ n : ℕ, |∫ ω, Φ (M t ω) ∂P - ∫ x, Φ x ∂γ| ≤
      (1 / 2) * J + (Real.sqrt (∫ x, ‖x - (HilbertCLTAux.denseSub (H := H) n).starProjection x‖ ^ 2
        ∂(law P (M t))) +
        Real.sqrt (∫ x, ‖x - (HilbertCLTAux.denseSub (H := H) n).starProjection x‖ ^ 2 ∂γ)) := by
    intro n
    set K := HilbertCLTAux.denseSub (H := H) n with hK
    obtain ⟨d, b, hb, hP⟩ := exists_orthonormal_proj K
    have fd := finite_dim_step P ht hM hsb hγ hb hΦ
    simp_rw [hP] at fd
    obtain ⟨hi1, hi2⟩ := hm_tail_bound (law P (M t)) hρ K
    obtain ⟨hj1, hj2⟩ := hm_tail_bound γ hGm K
    have t1 := HilbertCLTAux.lip_tail_bound (law P (M t)) K hC hlip hi1
    have t2 := HilbertCLTAux.lip_tail_bound γ K hC hlip hj1
    have e1 : ∫ x, Φ x ∂(law P (M t)) = ∫ ω, Φ (M t ω) ∂P :=
      integral_map hmt hΦc.aestronglyMeasurable
    have e2 : ∫ x, Φ (K.starProjection x) ∂(law P (M t)) = ∫ ω, Φ (K.starProjection (M t ω)) ∂P :=
      integral_map hmt (hΦc.comp K.starProjection.continuous).aestronglyMeasurable
    rw [e1, e2] at t1
    simp only [NNReal.coe_one, one_mul] at t1 t2
    have h3 := abs_add_three (∫ ω, Φ (M t ω) ∂P - ∫ ω, Φ (K.starProjection (M t ω)) ∂P)
      (∫ ω, Φ (K.starProjection (M t ω)) ∂P - ∫ x, Φ (K.starProjection x) ∂γ)
      (∫ x, Φ (K.starProjection x) ∂γ - ∫ x, Φ x ∂γ)
    have e3 : ∫ ω, Φ (M t ω) ∂P - ∫ x, Φ x ∂γ =
        (∫ ω, Φ (M t ω) ∂P - ∫ ω, Φ (K.starProjection (M t ω)) ∂P) +
        (∫ ω, Φ (K.starProjection (M t ω)) ∂P - ∫ x, Φ (K.starProjection x) ∂γ) +
        (∫ x, Φ (K.starProjection x) ∂γ - ∫ x, Φ x ∂γ) := by ring
    rw [e3]
    rw [abs_sub_comm (∫ x, Φ (K.starProjection x) ∂γ)] at h3
    have := t2
    linarith
  have hT : ∀ (ρ : Measure H) [IsProbabilityMeasure ρ], Integrable (fun x : H => ‖x‖ ^ 2) ρ →
      Tendsto (fun n => Real.sqrt (∫ x, ‖x - (HilbertCLTAux.denseSub (H := H) n).starProjection x‖ ^ 2
        ∂ρ)) atTop (𝓝 0) := by
    intro ρ _ hρ'
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp (HilbertCLTAux.denseSub_tail ρ hρ')
    rw [Real.sqrt_zero] at this
    exact this
  have hlim := tendsto_const_nhds (x := (1 / 2) * J) |>.add
    ((hT (law P (M t)) hρsq).add (hT γ hγsq))
  have := ge_of_tendsto' hlim key
  simpa using this

end A22Main

section A22Cond

lemma ae_le_of_setIntegral_le_trim {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
    (hfi : Integrable f P) (hgi : Integrable g P)
    (h : ∀ s, MeasurableSet[m] s → ∫ x in s, f x ∂P ≤ ∫ x in s, g x ∂P) : f ≤ᵐ[P] g := by
  have := @ae_le_of_forall_setIntegral_le Ω m (P.trim hm) f g (hfi.trim hm hf) (hgi.trim hm hg)
    (fun s hs _ => by
      rw [← setIntegral_trim hm hf hs, ← setIntegral_trim hm hg hs]
      exact h s hs)
  exact ae_of_ae_trim hm this

lemma martingale_cond {ℱ : Filtration ℝ mΩ} {f : ℝ → Ω → ℝ} (hf : Martingale f ℱ P)
    (h0 : f 0 =ᵐ[P] 0) {A : Set Ω}
    (hA : MeasurableSet[ℱ 0] A) (hP0 : P A ≠ 0) : Martingale f ℱ (ProbabilityTheory.cond P A) := by
  have hAm : MeasurableSet A := ℱ.le 0 _ hA
  refine ⟨hf.1, fun i j hij => ?_⟩
  have hmi : ℱ i ≤ mΩ := ℱ.le i
  have hint : ∀ k, Integrable (f k) (ProbabilityTheory.cond P A) := fun k =>
    ((hf.integrable k).restrict (s := A)).smul_measure (ENNReal.inv_ne_top.2 hP0)
  -- `f k = 0` a.s. for `k ≤ 0`
  have hneg : ∀ k, k ≤ 0 → f k =ᵐ[P] 0 := by
    intro k hk
    have h1 := hf.2 k 0 hk
    have h2 : P[f 0 | ℱ k] =ᵐ[P] P[(0 : Ω → ℝ) | ℱ k] := condExp_congr_ae h0
    rw [condExp_zero] at h2
    exact h1.symm.trans h2
  have hset : ∀ s, MeasurableSet[ℱ i] s → ∫ x in s ∩ A, f i x ∂P = ∫ x in s ∩ A, f j x ∂P := by
    intro s hs
    by_cases hi : 0 ≤ i
    · exact hf.setIntegral_eq hij (hs.inter (ℱ.mono hi _ hA))
    · push_neg at hi
      have hsA : MeasurableSet[ℱ 0] (s ∩ A) := ((ℱ.mono hi.le) _ hs).inter hA
      have e1 : ∫ x in s ∩ A, f i x ∂P = 0 := by
        rw [integral_congr_ae (ae_restrict_of_ae (hneg i hi.le))]; simp
      rw [e1]
      by_cases hj : 0 ≤ j
      · rw [← hf.setIntegral_eq hj hsA, integral_congr_ae (ae_restrict_of_ae h0)]; simp
      · push_neg at hj
        rw [integral_congr_ae (ae_restrict_of_ae (hneg j hj.le))]; simp
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hmi (hint j) (fun s _ _ => (hint i).integrableOn)
    (fun s hs _ => ?_) (hf.1 i).aestronglyMeasurable
  have hsm : MeasurableSet s := hmi _ hs
  simp only [ProbabilityTheory.cond, Measure.restrict_smul, integral_smul_measure]
  rw [Measure.restrict_restrict hsm, hset s hs]

lemma isHilbertMartingale_cond {ℱ : Filtration ℝ mΩ} {t : ℝ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hP0 : P A ≠ 0) :
    IsHilbertMartingaleWithCovariation (ProbabilityTheory.cond P A) ℱ t M Sg := by
  have hac : ProbabilityTheory.cond P A ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  have hc : (P A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hP0
  have hzero : ∀ x : H, (fun ω => inner ℝ (M 0 ω) x) =ᵐ[P] 0 := fun x => by
    filter_upwards [hM.zero] with ω h
    simp [h]
  refine
    { martingale := fun x => martingale_cond P (hM.martingale x) (hzero x) hA hP0
      zero := hac.ae_le hM.zero
      cont := hac.ae_le hM.cont
      sq_int := fun τ hτ => ?_
      sigma_meas := hM.sigma_meas
      sigma_adapted := hM.sigma_adapted
      sigma_traceClass := hac.ae_le hM.sigma_traceClass
      sigma_int := ?_
      sigma_pathint := hac.ae_le hM.sigma_pathint
      sigma_entry_int := hac.ae_le hM.sigma_entry_int
      covariation := fun x y => ?_ }
  · exact ((hM.sq_int τ hτ).restrict A).smul_measure hc
  · exact (hM.sigma_int.restrict (s := A)).smul_measure hc
  · refine martingale_cond P (hM.covariation x y) ?_ hA hP0
    filter_upwards [hM.zero] with ω h
    simp [h]

end A22Cond

/-- Lemma A.22 `M:B:lem:hilbert-martingale-clt` (source lines 10600-10611), bound
`B:eq:hilbert-martingale-clt`: for a continuous square-integrable `H`-valued martingale `M`
with `M_0 = 0` and tensor quadratic variation `∫_0^t Σ_r dr` (`Σ_r ≥ 0` trace class,
`E ∫_0^t ‖Σ_r‖_{𝔖₁} < ∞`), a deterministic nonnegative trace-class integrable `Σ̄`, and `G`
the centered Gaussian element of `H` with covariance `∫_0^t Σ̄_r dr`,
`d_{C²}(Law M_t, Law G) ≤ ½ E ∫_0^t ‖Σ_r - Σ̄_r‖_{𝔖₁} dr`.

PLAN (proof route, source lines 10613-10620): fix a Hilbert basis `e : ℕ → H`
(`HilbertCLTAux.exists_hilbertBasis_type`) and the projections `P_n` onto `span (e_0, …, e_{n-1})`.
The coordinate process `(⟨M, e_a⟩)_{a < n}` is an `ℝ^n`-valued martingale with covariation matrix
`(Σ_r(e_a, e_b))_{ab}` (`IsVectorMartingaleWithCovariation`; the fields follow from the
coordinatewise fields here and `traceNormMatrix ≤ traceNormForm` for the compression), so
`multivariate_martingale_clt_dc2` gives the bound for `P_n M_t` and `P_n G` (the Gaussian
`multivariateGaussian 0 (∫ Σ̄(e_a,e_b))` is the law of the coordinates of `G`, by
`IsCenteredGaussian` and `covarianceBilin`).  Compression is contractive in trace norm:
`traceNormMatrix (Σ(e_a,e_b))_{a,b<n} ≤ traceNormForm Σ` (directly from the variational formulas,
`le_traceNormMatrix`/`traceNormMatrix_bddAbove`).  For a test function `Φ ∈ CbUnitBall H 2`,
`|E Φ(M_t) - E Φ(P_n M_t)| ≤ E ‖(I - P_n) M_t‖` (`norm_sub_le_of_mem_one`, `cbUnitBall_anti`),
and `E ‖(I - P_n) M_t‖² = ∑_{k ≥ n} E ⟨M_t, e_k⟩² = ∑_{k≥n} E ∫_0^t Σ_r(e_k,e_k) dr → 0` by the
`covariation` martingale at `τ = t` (`integral_mul_martingale`-type lemmas in
`HRS/Prob/MartingaleLindeberg.lean`) and `IsTraceClassCov.trace` with dominated/monotone
convergence; the Gaussian tail `E ‖(I-P_n) G‖² = ∑_{k ≥ n} ∫ Σ̄(e_k,e_k)` likewise
(`HilbertCLTAux.gaussian_tail_bound`, `hasSum_cov_basis`).  Pass `n → ∞`.  Uses
`smoothDist_le`-type transfer of `smoothDist 2` between `H` restricted to `range P_n` and
`ℝ^n` (`Φ ∘ ι_n ∈ CbUnitBall (ℝ^n) 2` for the isometry `ι_n`). -/
theorem hilbert_martingale_clt (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb)
    (γ : Measure H) (hγ : IsGaussianWithIntegratedCov t sb γ) :
    smoothDist 2 (law P (M t)) γ ≤ (1 / 2) * covDiscrepancy P t Sg sb := by
  have hmt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hJ0 : 0 ≤ covDiscrepancy P t Sg sb :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  have e : ∫ z, Φ.1 z ∂(law P (M t)) = ∫ ω, Φ.1 (M t ω) ∂P :=
    integral_map hmt Φ.2.1.continuous.aestronglyMeasurable
  rw [e]
  exact hilbert_clt_core P ht hM hsb hγ Φ.2

/-- Lemma A.22, last sentence (source line 10610): "the same assertion holds conditionally on
an initial sigma-field `𝒢 ⊂ ℱ_0`", i.e. for every test function `Φ` of the `d_{C²}` class,
almost surely `|E[Φ(M_t) | 𝒢] - E[Φ(G)]| ≤ ½ E[∫_0^t ‖Σ_r - Σ̄_r‖_{𝔖₁} dr | 𝒢]`
(the conditional law of `M_t` given `𝒢` against the law of `G`; stated for each test function
because Mathlib has no regular conditional laws on `H`, cf. Lemma A.27 `B:newprob:conditional-bound`
which is stated in exactly this form).

PLAN: either (a) the argument of `hilbert_martingale_clt` with `∫ · dP` replaced by `P[· | 𝒢]`
throughout (the Lindeberg partition bound of `HRS/Prob/MartingaleLindeberg.lean` conditioned on
`𝒢 ⊆ ℱ_0`; this is the finite-dimensional `conditional_gaussian_interpolation` below with `X = 0`
after projecting on `span (e_0,…,e_{n-1})`), or (b) `conditional_gaussian_interpolation` applied
to the coordinates (with a Gaussian `G` independent of `ℱ_t` built on an enlargement,
`exists_enlargement`, and transported back since `P[·|𝒢]` is insensitive to independent
enlargement), followed by the same projection/tail argument conditionally. -/
theorem hilbert_martingale_clt_cond (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (𝒢 : InitialSigma ℱ)
    (M : ℝ → Ω → H) (Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ))
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M Sg)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb)
    (γ : Measure H) (hγ : IsGaussianWithIntegratedCov t sb γ)
    (Φ : H → ℝ) (hΦ : Φ ∈ CbUnitBall H 2) :
    ∀ᵐ ω ∂P,
      |(P[fun ω => Φ (M t ω) | 𝒢.1]) ω - ∫ z, Φ z ∂γ| ≤
        (1 / 2) * (P[fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ) | 𝒢.1]) ω := by
  have hm : 𝒢.1 ≤ mΩ := 𝒢.2.trans (ℱ.le 0)
  have hmt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  set X : Ω → ℝ := fun ω => Φ (M t ω) with hX
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 t, traceNormForm (Sg σ ω - sb σ) with hg
  set c : ℝ := ∫ z, Φ z ∂γ with hc
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hXint : Integrable X P :=
    Integrable.of_bound (C := 1) (hΦc.measurable.comp_aemeasurable hmt).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using abs_apply_le_of_mem hΦ (M t ω))
  have hgint : Integrable g P := discrepancy_integrable P hM hsb
  -- the weighted inequality on sets of `𝒢`
  have hSA : ∀ A, MeasurableSet[𝒢.1] A →
      |(∫ ω in A, X ω ∂P) - P.real A * c| ≤ (1 / 2) * ∫ ω in A, g ω ∂P := by
    intro A hA
    have hAm : MeasurableSet A := hm _ hA
    by_cases hP0 : P A = 0
    · have : P.restrict A = 0 := Measure.restrict_eq_zero.2 hP0
      simp [this, Measure.real, hP0]
    · have hAℱ : MeasurableSet[ℱ 0] A := 𝒢.2 _ hA
      have : IsProbabilityMeasure (ProbabilityTheory.cond P A) :=
        ProbabilityTheory.cond_isProbabilityMeasure hP0
      have hMc := isHilbertMartingale_cond P hM hAℱ hP0
      have hcore := hilbert_clt_core (ProbabilityTheory.cond P A) ht hMc hsb hγ hΦ
      have hI : ∀ F : Ω → ℝ, ∫ ω, F ω ∂(ProbabilityTheory.cond P A) =
          ((P A).toReal)⁻¹ * ∫ ω in A, F ω ∂P := by
        intro F
        simp [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
      unfold covDiscrepancy at hcore
      rw [hI, hI] at hcore
      have hp : 0 < (P A).toReal := ENNReal.toReal_pos hP0 (measure_ne_top P A)
      have hpr : P.real A = (P A).toReal := rfl
      rw [hpr]
      have e1 : (∫ ω in A, X ω ∂P) - (P A).toReal * c =
          (P A).toReal * (((P A).toReal)⁻¹ * ∫ ω in A, X ω ∂P - c) := by
        field_simp
      rw [e1, abs_mul, abs_of_pos hp]
      calc (P A).toReal * |((P A).toReal)⁻¹ * ∫ ω in A, X ω ∂P - c|
          ≤ (P A).toReal * ((1 / 2) * (((P A).toReal)⁻¹ * ∫ ω in A, g ω ∂P)) :=
            mul_le_mul_of_nonneg_left hcore hp.le
        _ = _ := by field_simp
  set U := P[X | 𝒢.1] with hU
  set V := P[g | 𝒢.1] with hV
  have hUm : StronglyMeasurable[𝒢.1] U := stronglyMeasurable_condExp
  have hVm : StronglyMeasurable[𝒢.1] V := stronglyMeasurable_condExp
  have hUi : Integrable U P := integrable_condExp
  have hVi : Integrable V P := integrable_condExp
  have hsetU : ∀ A, MeasurableSet[𝒢.1] A → ∫ ω in A, U ω ∂P = ∫ ω in A, X ω ∂P :=
    fun A hA => setIntegral_condExp hm hXint hA
  have hsetV : ∀ A, MeasurableSet[𝒢.1] A → ∫ ω in A, V ω ∂P = ∫ ω in A, g ω ∂P :=
    fun A hA => setIntegral_condExp hm hgint hA
  have hconst : ∀ A, MeasurableSet A → ∫ ω in A, c ∂P = P.real A * c := fun A hA => by
    rw [setIntegral_const, smul_eq_mul]
  have h1 : (fun ω => U ω - c) ≤ᵐ[P] fun ω => (1 / 2) * V ω := by
    refine ae_le_of_setIntegral_le_trim P hm (hUm.sub stronglyMeasurable_const)
      (hVm.const_mul _) (hUi.sub (integrable_const c)) (hVi.const_mul _) ?_
    intro A hA
    have hAm : MeasurableSet A := hm _ hA
    rw [integral_sub hUi.integrableOn (integrable_const c).integrableOn, integral_const_mul,
      hsetU A hA, hsetV A hA, hconst A hAm]
    have := hSA A hA
    rw [abs_le] at this
    linarith [this.2]
  have h2 : (fun ω => c - U ω) ≤ᵐ[P] fun ω => (1 / 2) * V ω := by
    refine ae_le_of_setIntegral_le_trim P hm (stronglyMeasurable_const.sub hUm)
      (hVm.const_mul _) ((integrable_const c).sub hUi) (hVi.const_mul _) ?_
    intro A hA
    have hAm : MeasurableSet A := hm _ hA
    rw [integral_sub (integrable_const c).integrableOn hUi.integrableOn, integral_const_mul,
      hsetU A hA, hsetV A hA, hconst A hAm]
    have := hSA A hA
    rw [abs_le] at this
    linarith [this.1]
  filter_upwards [h1, h2] with ω a b
  rw [abs_le]
  constructor <;> linarith

end HilbertMartingale

/-! ### Cylindrical Brownian motions, Hilbert–Schmidt integrands and `H`-valued Itô integrals -/

section Cylindrical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- A `U`-cylindrical Brownian motion with respect to `ℱ`, through a Hilbert basis `(u_k)_{k∈κ}`
of the separable space `U`: the real processes `W^k_t = W_t(u_k)` form, for every finite set of
indices, a family of independent standard Brownian motions relative to `ℱ`
(`IsBrownianFiltration`, `HRS/Stochastic/Brownian.lean`). -/
def IsCylindricalBrownian (ℱ : Filtration ℝ mΩ) {κ : Type*} [Countable κ]
    (W : ℝ≥0 → Ω → κ → ℝ) : Prop :=
  ∀ s : Finset κ, IsBrownianFiltration P ℱ (fun t ω (k : s) => W t ω k)

/-- The `L²` size `E ∫_0^t ∑_k ‖Φ_r u_k‖² dr = E ∫_0^t ‖Φ_r‖²_{𝓛₂(U,H)} dr` in `ℝ≥0∞`. -/
def hsSqIntegralOn {κ : Type*} (Φ : ℝ → Ω → κ → H) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑' k, ‖Φ r ω k‖ₑ ^ 2) ∂P

/-- A progressive Hilbert–Schmidt integrand `Φ : Ω × [0,t] → 𝓛₂(U,H)` with
`E ∫_0^t ‖Φ_r‖²_{𝓛₂(U,H)} dr < ∞` (Corollary A.23, lines 10631-10633; "predictable" in the
source, progressive here), given through `Φ_r u_k`. -/
structure IsHSIntegrand (ℱ : Filtration ℝ mΩ) (t : ℝ) {κ : Type*} (Φ : ℝ → Ω → κ → H) :
    Prop where
  prog : ∀ k, IsProgressive ℱ (fun r ω => Φ r ω k)
  summable : ∀ r ω, Summable fun k => ‖Φ r ω k‖ ^ 2
  sq : hsSqIntegralOn P Φ t < ∞

/-- `M = ∫_0^· Φ_r dW_r` as an `H`-valued process: continuous, adapted, zero on `(-∞,0]`, and
for every `x ∈ H` and `τ ≥ 0` the coordinate `⟨M_τ, x⟩` is the `L²(P)`-limit of the finite sums
`∑_{k ∈ s} ∫_0^τ ⟨Φ_r u_k, x⟩ dW^k_r` of real Itô integrals (`HRS.itoIntegral`) along the
directed family of finite sets `s`. -/
structure IsHilbertItoIntegral (ℱ : Filtration ℝ mΩ) {κ : Type*} (W : ℝ≥0 → Ω → κ → ℝ)
    (Φ : ℝ → Ω → κ → H) (M : ℝ → Ω → H) : Prop where
  cont : ∀ ω, Continuous fun τ => M τ ω
  adapted : Adapted ℱ M
  zero : ∀ τ : ℝ, τ ≤ 0 → ∀ ω, M τ ω = 0
  approx : ∀ τ : ℝ, 0 ≤ τ → ∀ x : H,
    Tendsto (fun s : Finset κ => ∫⁻ ω,
        ‖itoIntegral P ℱ (fun t ω (k : s) => W t ω k) (fun r ω (k : s) => inner ℝ (Φ r ω k) x) τ ω
          - inner ℝ (M τ ω) x‖ₑ ^ 2 ∂P) atTop (𝓝 0)

end Cylindrical

/-! ### Auxiliary development for Corollary A.23 (polar decomposition, countable Ito integrals)

Route: see the plan in the docstring of `hilbert_polar_coupling`.  This block holds the finished
(sorry-free) pieces, all independent of the frozen statement:
* measurable polar decomposition with Powers-Stormer (`exists_polar_coords`, `powers_stormer`) and its
  packaging for a progressive Hilbert-Schmidt integrand (`exists_polar_family`: the square roots
  `S r ω`, and the orthonormal coefficient family `ψ j r ω a`, `a : κ ⊕ ι`, with the coordinate
  expansions needed for the identification of `M` and for the tail estimates);
* the infinite family of independent Wiener sequences (`wMeasure`, `wFiltration`,
  `isBrownianFiltration_wFiltration`) and the product filtration (`prodFiltration`), with
  `isCylindricalBrownian_prod` (the family `W ∘ fst ⊕ Wiener` is cylindrical Brownian for the product
  filtration, by Levy) and `IsCylindricalBrownian.comp_inj` (reindexing along injections);
* the countable-index Ito integral `IsItoC` (existence, uniqueness, linearity, isometry, martingale,
  conditional isometry, `IsItoC.martingale_sq_sub`, `IsItoC.martingale_mul_sub_const`, pull-out
  `IsItoC.block`, finite sums `IsItoC.finset_sum`, elementary integrals `isItoC_elem`);
* associativity `isItoIntegral_assoc`: for orthonormal `ψ` and `B^j = ∫ψ^j d𝔚`, the Ito integral
  of `f` against `B` is `∫ (∑_j f_j ψ^j) d𝔚`; and `isCylindricalBrownian_of_itoC` (`B` is cylindrical
  Brownian, by Levy);
* transfer along a measure-preserving map with filtration pull-back (`itoIntegral_comp_π`), and
  `indep_zero_cylPath` (a cylindrical Brownian motion is independent of `ℱ 0`).
Still to do for a repaired statement (see the attempt-4 finding below): the `H`-valued continuous version
of `∫ Sb dB` (Doob `doob_L2_continuous` coordinatewise, `∑_i sup|G^i|² < ∞` a.s.), its Gaussianity and
independence of `𝒢` (via `dds_coupling_strong` under the conditional measures `P'(· | A)`, `A ∈ ℱ' 0`,
then `Measure.ext_of_charFun`), the transfer of `hM` through `itoIntegral_pad` and `itoIntegral_comp_π`,
the `L²` bound (isometry for `B`, `powers_stormer`), and the universe lift of the Hilbert basis index. -/

section FragP1
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
section PolarOps
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Scalar comparison sequence for the square-root iteration. -/
def sqrtScalar : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 + sqrtScalar n ^ 2) / 2

lemma sqrtScalar_nonneg : ∀ n, 0 ≤ sqrtScalar n
  | 0 => le_rfl
  | n + 1 => by simp only [sqrtScalar]; have := sqrtScalar_nonneg n; positivity

lemma sqrtScalar_le_one : ∀ n, sqrtScalar n ≤ 1
  | 0 => by simp [sqrtScalar]
  | n + 1 => by
      simp only [sqrtScalar]
      have h0 := sqrtScalar_nonneg n
      have h1 := sqrtScalar_le_one n
      nlinarith

lemma sqrtScalar_mono : Monotone sqrtScalar := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [sqrtScalar]
  nlinarith [sq_nonneg (sqrtScalar n - 1)]

/-- The iteration `Z_{n+1} = (D + Z_n²)/2`, `Z_0 = 0`. -/
def sqrtIter (D : H →L[ℝ] H) : ℕ → H →L[ℝ] H
  | 0 => 0
  | n + 1 => (1 / 2 : ℝ) • (D + sqrtIter D n * sqrtIter D n)

omit [CompleteSpace H] in
lemma norm_sqrtIter_le {D : H →L[ℝ] H} (hD : ‖D‖ ≤ 1) : ∀ n, ‖sqrtIter D n‖ ≤ sqrtScalar n
  | 0 => by simp [sqrtIter, sqrtScalar]
  | n + 1 => by
      have ih := norm_sqrtIter_le hD n
      simp only [sqrtIter, sqrtScalar]
      calc ‖(1 / 2 : ℝ) • (D + sqrtIter D n * sqrtIter D n)‖
          = (1 / 2) * ‖D + sqrtIter D n * sqrtIter D n‖ := by
            rw [norm_smul]; norm_num
        _ ≤ (1 / 2) * (‖D‖ + ‖sqrtIter D n‖ * ‖sqrtIter D n‖) := by
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ (1 + sqrtScalar n ^ 2) / 2 := by
            have := sqrtScalar_nonneg n
            nlinarith [norm_nonneg (sqrtIter D n)]

omit [CompleteSpace H] in
lemma norm_sqrtIter_succ_sub_le {D : H →L[ℝ] H} (hD : ‖D‖ ≤ 1) :
    ∀ n, ‖sqrtIter D (n + 1) - sqrtIter D n‖ ≤ sqrtScalar (n + 1) - sqrtScalar n
  | 0 => by
      simp only [sqrtIter, sqrtScalar, mul_zero, add_zero, sub_zero, norm_smul]
      norm_num
      linarith
  | n + 1 => by
      have ih := norm_sqrtIter_succ_sub_le hD n
      have h1 := norm_sqrtIter_le hD n
      have h2 := norm_sqrtIter_le hD (n + 1)
      have e : sqrtIter D (n + 1 + 1) - sqrtIter D (n + 1) =
          (1 / 2 : ℝ) • ((sqrtIter D (n + 1) - sqrtIter D n) * sqrtIter D (n + 1) +
            sqrtIter D n * (sqrtIter D (n + 1) - sqrtIter D n)) := by
        show (1 / 2 : ℝ) • (D + sqrtIter D (n + 1) * sqrtIter D (n + 1)) -
          (1 / 2 : ℝ) • (D + sqrtIter D n * sqrtIter D n) = _
        rw [← smul_sub]
        congr 1
        simp only [mul_sub, sub_mul]
        abel
      rw [e, norm_smul]
      have h3 : ‖(sqrtIter D (n + 1) - sqrtIter D n) * sqrtIter D (n + 1) +
            sqrtIter D n * (sqrtIter D (n + 1) - sqrtIter D n)‖ ≤
          (sqrtScalar (n + 1) - sqrtScalar n) * (sqrtScalar (n + 1) + sqrtScalar n) := by
        refine (norm_add_le _ _).trans ?_
        have a1 := ContinuousLinearMap.opNorm_comp_le (sqrtIter D (n + 1) - sqrtIter D n)
          (sqrtIter D (n + 1))
        have a2 := ContinuousLinearMap.opNorm_comp_le (sqrtIter D n)
          (sqrtIter D (n + 1) - sqrtIter D n)
        have := sqrtScalar_nonneg n
        have := sqrtScalar_nonneg (n + 1)
        have hm := sqrtScalar_mono (Nat.le_succ n)
        simp only [ContinuousLinearMap.mul_def] at *
        nlinarith [norm_nonneg (sqrtIter D n), norm_nonneg (sqrtIter D (n + 1)),
          norm_nonneg (sqrtIter D (n + 1) - sqrtIter D n),
          mul_le_mul_of_nonneg_right ih (norm_nonneg (sqrtIter D (n + 1))),
          mul_le_mul_of_nonneg_left ih (norm_nonneg (sqrtIter D n)),
          mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 hm),
          mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hm)]
      have : sqrtScalar (n + 1 + 1) - sqrtScalar (n + 1) =
          (1 / 2) * ((sqrtScalar (n + 1) - sqrtScalar n) * (sqrtScalar (n + 1) + sqrtScalar n)) := by
        simp only [sqrtScalar]; ring
      rw [this]
      norm_num
      linarith

lemma cauchySeq_sqrtIter {D : H →L[ℝ] H} (hD : ‖D‖ ≤ 1) : CauchySeq (sqrtIter D) := by
  refine cauchySeq_of_dist_le_of_summable (fun n => sqrtScalar (n + 1) - sqrtScalar n)
    (fun n => ?_) ?_
  · rw [dist_comm, dist_eq_norm]; exact norm_sqrtIter_succ_sub_le hD n
  · refine summable_of_sum_range_le (c := 1) (fun n => sub_nonneg.2 (sqrtScalar_mono (Nat.le_succ n)))
      fun n => ?_
    rw [Finset.sum_range_sub]
    have := sqrtScalar_le_one n
    have := sqrtScalar_nonneg 0
    linarith


section SqrtOp
open HilbertCLTAux

omit [CompleteSpace H] in
lemma HilbertCLTAux.IsPSDOp.norm_apply_le {D : H →L[ℝ] H} (hD : IsPSDOp D) (h : ∀ x, inner ℝ (D x) x ≤ ‖x‖ ^ 2)
    (x : H) : ‖D x‖ ≤ ‖x‖ := by
  have h1 := hD.cs x (D x)
  have h2 := h (D x)
  have h3 := h x
  have h5 : inner ℝ (D x) (D x) = ‖D x‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [h5] at h1
  have h6 : ‖D x‖ ^ 2 * ‖D x‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖D x‖ ^ 2 := by
    calc ‖D x‖ ^ 2 * ‖D x‖ ^ 2 = (‖D x‖ ^ 2) ^ 2 := by ring
      _ ≤ _ := h1
      _ ≤ ‖x‖ ^ 2 * ‖D x‖ ^ 2 := mul_le_mul h3 h2 (hD.nonneg _) (sq_nonneg _)
  by_cases hz : ‖D x‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hp : 0 < ‖D x‖ ^ 2 := by positivity
    have := le_of_mul_le_mul_right h6 hp
    nlinarith [norm_nonneg x, norm_nonneg (D x)]


/-- The limit of the iteration. -/
def sqrtLimOp (D : H →L[ℝ] H) : H →L[ℝ] H := limUnder atTop (sqrtIter D)

lemma tendsto_sqrtIter {D : H →L[ℝ] H} (hD : ‖D‖ ≤ 1) :
    Tendsto (sqrtIter D) atTop (𝓝 (sqrtLimOp D)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_sqrtIter hD))

lemma tendsto_sqrtIter_apply {D : H →L[ℝ] H} (hD : ‖D‖ ≤ 1) (x : H) :
    Tendsto (fun n => sqrtIter D n x) atTop (𝓝 (sqrtLimOp D x)) :=
  ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto _).comp (tendsto_sqrtIter hD)

omit [CompleteSpace H] in
lemma sqrtIter_symm {D : H →L[ℝ] H} (hD : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y)) :
    ∀ n x y, inner ℝ (sqrtIter D n x) y = inner ℝ x (sqrtIter D n y)
  | 0, x, y => by simp [sqrtIter]
  | n + 1, x, y => by
      have ih := sqrtIter_symm hD n
      simp only [sqrtIter, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.mul_apply, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, hD, ih]
      simp

lemma sqrtLimOp_symm {D : H →L[ℝ] H} (hD : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (hD1 : ‖D‖ ≤ 1) (x y : H) : inner ℝ (sqrtLimOp D x) y = inner ℝ x (sqrtLimOp D y) := by
  have h1 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_sqrtIter_apply hD1 x) (tendsto_const_nhds (x := y))
  have h2 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := x)) (tendsto_sqrtIter_apply hD1 y)
  refine tendsto_nhds_unique h1 ?_
  simpa [sqrtIter_symm hD] using h2

lemma norm_sqrtLimOp_le {D : H →L[ℝ] H} (hD1 : ‖D‖ ≤ 1) : ‖sqrtLimOp D‖ ≤ 1 :=
  le_of_tendsto ((tendsto_sqrtIter hD1).norm) (Eventually.of_forall fun n =>
    (norm_sqrtIter_le hD1 n).trans (sqrtScalar_le_one n))

lemma sqrtLimOp_eq {D : H →L[ℝ] H} (hD1 : ‖D‖ ≤ 1) :
    sqrtLimOp D = (1 / 2 : ℝ) • (D + sqrtLimOp D * sqrtLimOp D) := by
  have h1 := (tendsto_sqrtIter hD1)
  have h2 : Tendsto (fun n => sqrtIter D (n + 1)) atTop (𝓝 (sqrtLimOp D)) :=
    h1.comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun n => sqrtIter D (n + 1)) atTop
      (𝓝 ((1 / 2 : ℝ) • (D + sqrtLimOp D * sqrtLimOp D))) :=
    (tendsto_const_nhds.add (h1.mul h1)).const_smul _
  exact tendsto_nhds_unique h2 h3

/-- The square root `Y = 1 - lim Z_n` of `1 - D`. -/
lemma sqrt_aux {D : H →L[ℝ] H} (hDs : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y)) (hD1 : ‖D‖ ≤ 1) :
    IsPSDOp (1 - sqrtLimOp D) ∧ (1 - sqrtLimOp D) * (1 - sqrtLimOp D) = 1 - D := by
  have hs := sqrtLimOp_symm hDs hD1
  have hn := norm_sqrtLimOp_le hD1
  refine ⟨⟨fun x y => ?_, fun x => ?_⟩, ?_⟩
  · simp [inner_sub_left, inner_sub_right, hs]
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, inner_sub_left]
    have h1 : inner ℝ (sqrtLimOp D x) x ≤ ‖x‖ ^ 2 := by
      calc inner ℝ (sqrtLimOp D x) x ≤ ‖sqrtLimOp D x‖ * ‖x‖ := real_inner_le_norm _ _
        _ ≤ (‖sqrtLimOp D‖ * ‖x‖) * ‖x‖ := by
          gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    rw [real_inner_self_eq_norm_sq]; linarith
  · have e := sqrtLimOp_eq hD1
    have e2 : sqrtLimOp D * sqrtLimOp D = (2 : ℝ) • sqrtLimOp D - D := by
      have := congrArg (fun T => (2 : ℝ) • T) e
      simp only [smul_smul] at this
      norm_num at this
      rw [this]; abel
    calc (1 - sqrtLimOp D) * (1 - sqrtLimOp D)
        = 1 - (2 : ℝ) • sqrtLimOp D + sqrtLimOp D * sqrtLimOp D := by
          simp only [mul_sub, sub_mul, one_mul, mul_one, two_smul]; abel
      _ = 1 - D := by rw [e2]; abel


/-- Square root of a nonnegative symmetric operator, with scale `c`. -/
def sqrtOp (c : ℝ) (A : H →L[ℝ] H) : H →L[ℝ] H :=
  Real.sqrt c • (1 - sqrtLimOp (1 - c⁻¹ • A))

omit [CompleteSpace H] in
lemma norm_one_sub_inv_smul_le {A : H →L[ℝ] H} (hA : IsPSDOp A) {c : ℝ} (hc : 0 < c)
    (hAc : ∀ x, inner ℝ (A x) x ≤ c * ‖x‖ ^ 2) : ‖(1 : H →L[ℝ] H) - c⁻¹ • A‖ ≤ 1 := by
  have hD : IsPSDOp ((1 : H →L[ℝ] H) - c⁻¹ • A) := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left, inner_sub_right,
        inner_smul_right, conj_trivial, hA.symm x y]
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left, conj_trivial,
        real_inner_self_eq_norm_sq]
      have := hAc x
      have h2 : c⁻¹ * inner ℝ (A x) x ≤ ‖x‖ ^ 2 := by
        calc c⁻¹ * inner ℝ (A x) x ≤ c⁻¹ * (c * ‖x‖ ^ 2) := by gcongr
          _ = ‖x‖ ^ 2 := by field_simp
      linarith
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul]
  refine hD.norm_apply_le (fun y => ?_) x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left, conj_trivial,
    real_inner_self_eq_norm_sq]
  have := hA.nonneg y
  have : 0 ≤ c⁻¹ * inner ℝ (A y) y := by positivity
  linarith

lemma sqrtOp_spec {A : H →L[ℝ] H} (hA : IsPSDOp A) {c : ℝ} (hc : 0 < c)
    (hAc : ∀ x, inner ℝ (A x) x ≤ c * ‖x‖ ^ 2) :
    IsPSDOp (sqrtOp c A) ∧ sqrtOp c A * sqrtOp c A = A := by
  have hD1 := norm_one_sub_inv_smul_le hA hc hAc
  have hDs : ∀ x y, inner ℝ (((1 : H →L[ℝ] H) - c⁻¹ • A) x) y =
      inner ℝ x (((1 : H →L[ℝ] H) - c⁻¹ • A) y) := fun x y => by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply, inner_sub_left, inner_smul_left, inner_sub_right,
        inner_smul_right, conj_trivial, hA.symm x y]
  obtain ⟨hY, hYY⟩ := sqrt_aux hDs hD1
  refine ⟨⟨fun x y => ?_, fun x => ?_⟩, ?_⟩
  · simp only [sqrtOp, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      conj_trivial, hY.symm x y]
  · simp only [sqrtOp, ContinuousLinearMap.smul_apply, inner_smul_left, conj_trivial]
    exact mul_nonneg (Real.sqrt_nonneg _) (hY.nonneg x)
  · have : sqrtOp c A * sqrtOp c A = (Real.sqrt c * Real.sqrt c) •
        ((1 - sqrtLimOp ((1 : H →L[ℝ] H) - c⁻¹ • A)) * (1 - sqrtLimOp ((1 : H →L[ℝ] H) - c⁻¹ • A))) := by
      simp only [sqrtOp, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [this, hYY, Real.mul_self_sqrt hc.le]
    ext x
    simp [hc.ne']

end SqrtOp

section OpMeas
variable [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Z : Type*} [MeasurableSpace Z]

/-- `z ↦ A z` is a strongly measurable operator family. -/
def OpMeas (A : Z → H →L[ℝ] H) : Prop := ∀ x, Measurable fun z => A z x

lemma measurable_of_inner_basis {ι : Type*} [Countable ι] (b : HilbertBasis ι ℝ H) {f : Z → H}
    (hf : ∀ i, Measurable fun z => inner ℝ (b i) (f z)) : Measurable f := by
  have hs : ∀ z, Tendsto (fun s : Finset ι => ∑ i ∈ s, inner ℝ (b i) (f z) • b i) atTop (𝓝 (f z)) :=
    fun z => by
      have := b.hasSum_repr (f z)
      simp only [HilbertBasis.repr_apply_apply] at this
      exact this
  refine measurable_of_tendsto_metrizable' atTop (fun s => ?_) (tendsto_pi_nhds.2 hs)
  exact Finset.measurable_sum _ fun i _ => (hf i).smul_const _

lemma OpMeas.apply {A : Z → H →L[ℝ] H} (hA : OpMeas A) {v : Z → H} (hv : Measurable v) :
    Measurable fun z => A z (v z) := by
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  have hs : ∀ z, Tendsto (fun s : Finset ι => ∑ i ∈ s, inner ℝ (b i) (v z) • A z (b i)) atTop
      (𝓝 (A z (v z))) := fun z => by
    have := (b.hasSum_repr (v z)).map (A z) (A z).continuous
    simp only [Function.comp_def, map_smul, HilbertBasis.repr_apply_apply] at this
    exact this
  refine measurable_of_tendsto_metrizable' atTop (fun s => ?_) (tendsto_pi_nhds.2 hs)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_const.inner hv).smul (hA (b i))

section
variable {A B : Z → H →L[ℝ] H}

lemma OpMeas.add (hA : OpMeas A) (hB : OpMeas B) : OpMeas fun z => A z + B z :=
  fun x => (hA x).add (hB x)

lemma OpMeas.sub (hA : OpMeas A) (hB : OpMeas B) : OpMeas fun z => A z - B z :=
  fun x => (hA x).sub (hB x)

lemma OpMeas.smul {c : Z → ℝ} (hc : Measurable c) (hA : OpMeas A) : OpMeas fun z => c z • A z :=
  fun x => hc.smul (hA x)

lemma OpMeas.const (T : H →L[ℝ] H) : OpMeas fun _ : Z => T := fun _ => measurable_const

lemma OpMeas.mul (hA : OpMeas A) (hB : OpMeas B) : OpMeas fun z => A z * B z :=
  fun x => hA.apply (hB x)

lemma OpMeas.sqrtIter {D : Z → H →L[ℝ] H} (hD : OpMeas D) :
    ∀ n, OpMeas fun z => sqrtIter (D z) n
  | 0 => by simpa [HRS.sqrtIter] using OpMeas.const (Z := Z) (0 : H →L[ℝ] H)
  | n + 1 => by
      have := ((hD.add ((OpMeas.sqrtIter hD n).mul (OpMeas.sqrtIter hD n)))).smul
        (measurable_const (a := (1 / 2 : ℝ)))
      simpa [HRS.sqrtIter] using this

lemma OpMeas.sqrtOp {c : Z → ℝ} (hA : OpMeas A) (hc : Measurable c)
    (hAp : ∀ z, HilbertCLTAux.IsPSDOp (A z)) (hcpos : ∀ z, 0 < c z)
    (hAc : ∀ z x, inner ℝ (A z x) x ≤ c z * ‖x‖ ^ 2) :
    OpMeas fun z => HRS.sqrtOp (c z) (A z) := by
  intro x
  have hD : OpMeas fun z => (1 : H →L[ℝ] H) - (c z)⁻¹ • A z :=
    OpMeas.sub (OpMeas.const 1) (OpMeas.smul hc.inv hA)
  have hlim : Measurable fun z => HRS.sqrtLimOp ((1 : H →L[ℝ] H) - (c z)⁻¹ • A z) x := by
    refine measurable_of_tendsto_metrizable (f := fun n z => HRS.sqrtIter ((1 : H →L[ℝ] H) - (c z)⁻¹ • A z) n x)
      (fun n => (OpMeas.sqrtIter hD n) x) (tendsto_pi_nhds.2 fun z => ?_)
    exact HRS.tendsto_sqrtIter_apply (norm_one_sub_inv_smul_le (hAp z) (hcpos z) (hAc z)) x
  simp only [HRS.sqrtOp, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]
  exact (Measurable.sqrt hc).smul (measurable_const.sub hlim)
end
end OpMeas

section PolarAbs
open HilbertCLTAux

omit [CompleteSpace H] in
lemma HilbertCLTAux.IsPSDOp.norm_apply_le' {D : H →L[ℝ] H} (hD : IsPSDOp D) {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ x, inner ℝ (D x) x ≤ m * ‖x‖ ^ 2) (x : H) : ‖D x‖ ≤ m * ‖x‖ := by
  have h1 := hD.cs x (D x)
  have h2 := h (D x)
  have h3 := h x
  have h5 : inner ℝ (D x) (D x) = ‖D x‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [h5] at h1
  have h6 : ‖D x‖ ^ 2 * ‖D x‖ ^ 2 ≤ (m * ‖x‖ ^ 2) * (m * ‖D x‖ ^ 2) := by
    calc ‖D x‖ ^ 2 * ‖D x‖ ^ 2 = (‖D x‖ ^ 2) ^ 2 := by ring
      _ ≤ _ := h1
      _ ≤ (m * ‖x‖ ^ 2) * (m * ‖D x‖ ^ 2) := mul_le_mul h3 h2 (hD.nonneg _) (by positivity)
  by_cases hz : ‖D x‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖D x‖ ^ 2 := by positivity
    have h7 : ‖D x‖ ^ 2 ≤ (m * ‖x‖) ^ 2 := by
      have : ‖D x‖ ^ 2 * ‖D x‖ ^ 2 ≤ ((m * ‖x‖) ^ 2) * ‖D x‖ ^ 2 := by
        calc _ ≤ _ := h6
          _ = _ := by ring
      exact le_of_mul_le_mul_right this hp
    exact le_of_sq_le_sq (by simpa using h7) (by positivity) |> fun h => by
      nlinarith [norm_nonneg (D x), mul_nonneg hm (norm_nonneg x)]


/-- The regularisation parameters `ε_n = 1/(n+1)`. -/
def epsn (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

lemma epsn_pos (n : ℕ) : 0 < epsn n := by unfold epsn; positivity

lemma tendsto_epsn : Tendsto epsn atTop (𝓝 0) := tendsto_inv_atTop_zero.comp
  (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

omit [CompleteSpace H] in
lemma HilbertCLTAux.IsPSDOp.inner_le_norm {S : H →L[ℝ] H} (x : H) :
    inner ℝ (S x) x ≤ ‖S‖ * ‖x‖ ^ 2 := by
  calc inner ℝ (S x) x ≤ ‖S x‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ (‖S‖ * ‖x‖) * ‖x‖ := by gcongr; exact S.le_opNorm x
    _ = _ := by ring

/-- `S + ε` is invertible for `S ≥ 0`, `ε > 0`. -/
lemma isUnit_add_smul_one {S : H →L[ℝ] H} (hS : IsPSDOp S) {ε : ℝ} (hε : 0 < ε) :
    IsUnit (S + ε • (1 : H →L[ℝ] H)) := by
  set c : ℝ := ‖S‖ + ε with hc
  have hcpos : 0 < c := by positivity
  set E : H →L[ℝ] H := 1 - c⁻¹ • (S + ε • (1 : H →L[ℝ] H)) with hE
  have hEapp : ∀ x, E x = x - c⁻¹ • (S x + ε • x) := fun x => by simp [hE]
  have hEinner : ∀ x, inner ℝ (E x) x = ‖x‖ ^ 2 - c⁻¹ * (inner ℝ (S x) x + ε * ‖x‖ ^ 2) := fun x => by
    rw [hEapp, inner_sub_left, inner_smul_left, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp
  have hEp : IsPSDOp E := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [hEapp, hEapp]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, conj_trivial, hS.symm x y]
    · rw [hEinner]
      have h1 := HilbertCLTAux.IsPSDOp.inner_le_norm (S := S) x
      have h2 : c⁻¹ * (inner ℝ (S x) x + ε * ‖x‖ ^ 2) ≤ c⁻¹ * (c * ‖x‖ ^ 2) := by
        gcongr
        nlinarith
      rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul] at h2
      linarith
  have hm : 0 ≤ 1 - ε / c := by
    rw [sub_nonneg, div_le_one hcpos]; rw [hc]; linarith [norm_nonneg S]
  have hEn : ‖E‖ ≤ 1 - ε / c := by
    refine ContinuousLinearMap.opNorm_le_bound _ hm fun x => ?_
    refine hEp.norm_apply_le' hm (fun y => ?_) x
    rw [hEinner]
    have h1 := hS.nonneg y
    have : c⁻¹ * (inner ℝ (S y) y + ε * ‖y‖ ^ 2) ≥ c⁻¹ * (ε * ‖y‖ ^ 2) := by
      gcongr; linarith
    have e : (1 - ε / c) * ‖y‖ ^ 2 = ‖y‖ ^ 2 - c⁻¹ * (ε * ‖y‖ ^ 2) := by field_simp
    linarith
  have hlt : ‖E‖ < 1 := by
    have : 0 < ε / c := by positivity
    linarith
  have h1E : IsUnit (1 - E) := (Units.oneSub E hlt).isUnit
  have : S + ε • (1 : H →L[ℝ] H) = c • (1 - E) := by
    rw [hE, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
  rw [this, Algebra.smul_def]
  exact (IsUnit.mk0 c hcpos.ne').map (algebraMap ℝ (H →L[ℝ] H)) |>.mul h1E


/-- The regularised resolvent `(S + ε_n)⁻¹`. -/
def resolvent (S : H →L[ℝ] H) (n : ℕ) : H →L[ℝ] H :=
  Ring.inverse (S + epsn n • (1 : H →L[ℝ] H))

section Resolvent
variable {S : H →L[ℝ] H} (hS : IsPSDOp S) (n : ℕ)
include hS

lemma resolvent_right (x : H) : S (resolvent S n x) + epsn n • resolvent S n x = x := by
  have h := Ring.mul_inverse_cancel _ (isUnit_add_smul_one hS (epsn_pos n))
  have := congrArg (fun T : H →L[ℝ] H => T x) h
  simpa [resolvent] using this

lemma resolvent_left (x : H) : resolvent S n (S x + epsn n • x) = x := by
  have h := Ring.inverse_mul_cancel _ (isUnit_add_smul_one hS (epsn_pos n))
  have := congrArg (fun T : H →L[ℝ] H => T x) h
  simpa [resolvent] using this

lemma norm_apply_le_add (w : H) {ε : ℝ} (hε : 0 ≤ ε) : ‖S w‖ ≤ ‖S w + ε • w‖ := by
  have h : ‖S w‖ ^ 2 ≤ ‖S w + ε • w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial]
    have h1 := hS.nonneg w
    have h2 : 0 ≤ inner ℝ w w := real_inner_self_nonneg
    have e := hS.symm w w
    nlinarith [mul_nonneg hε h1, mul_nonneg (mul_nonneg hε hε) h2]
  exact le_of_sq_le_sq (by simpa using h) (norm_nonneg _) |> fun h => by
    nlinarith [norm_nonneg (S w), norm_nonneg (S w + ε • w)]

lemma norm_S_resolvent_le (x : H) : ‖S (resolvent S n x)‖ ≤ ‖x‖ := by
  have := norm_apply_le_add hS (resolvent S n x) (epsn_pos n).le
  rwa [resolvent_right hS n x] at this

lemma resolvent_symm (x y : H) :
    inner ℝ (resolvent S n x) y = inner ℝ x (resolvent S n y) := by
  have e1 := resolvent_right hS n y
  have e2 := resolvent_right hS n x
  calc inner ℝ (resolvent S n x) y
      = inner ℝ (resolvent S n x) (S (resolvent S n y) + epsn n • resolvent S n y) := by rw [e1]
    _ = inner ℝ (S (resolvent S n x) + epsn n • resolvent S n x) (resolvent S n y) := by
        simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, conj_trivial,
          hS.symm (resolvent S n x) (resolvent S n y)]
    _ = _ := by rw [e2]

lemma resolvent_of_ker {x : H} (hx : S x = 0) : resolvent S n x = (epsn n)⁻¹ • x := by
  have := resolvent_left hS n ((epsn n)⁻¹ • x)
  rw [map_smul, hx, smul_zero, zero_add, smul_smul, mul_inv_cancel₀ (epsn_pos n).ne', one_smul] at this
  exact this

end Resolvent


section LimitOps
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

lemma exists_clm_of_tendsto (A : ℕ → E →L[ℝ] G) (hb : ∀ n x, ‖A n x‖ ≤ ‖x‖)
    (hconv : ∀ x, ∃ y, Tendsto (fun n => A n x) atTop (𝓝 y)) :
    ∃ L : E →L[ℝ] G, (∀ x, Tendsto (fun n => A n x) atTop (𝓝 (L x))) := by
  choose L hL using hconv
  let Lm : E →ₗ[ℝ] G :=
    { toFun := L
      map_add' := fun x y => tendsto_nhds_unique (hL (x + y)) (by
        have := (hL x).add (hL y)
        simpa using this)
      map_smul' := fun c x => tendsto_nhds_unique (hL (c • x)) (by
        have := (hL x).const_smul c
        simpa using this) }
  have hLb : ∀ x, ‖L x‖ ≤ 1 * ‖x‖ := fun x => by
    rw [one_mul]; exact le_of_tendsto' (hL x).norm (fun n => hb n x)
  exact ⟨Lm.mkContinuous 1 hLb, hL⟩

lemma tendsto_of_dense (A : ℕ → E →L[ℝ] G) (hb : ∀ n x, ‖A n x‖ ≤ ‖x‖) {D : Set E}
    (hD : Dense D) (hconv : ∀ x ∈ D, ∃ y, Tendsto (fun n => A n x) atTop (𝓝 y)) (x : E) :
    ∃ y, Tendsto (fun n => A n x) atTop (𝓝 y) := by
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff']
  intro δ hδ
  obtain ⟨x', hx'D, hx'⟩ := hD.exists_dist_lt x (show 0 < δ / 3 by positivity)
  obtain ⟨y, hy⟩ := hconv x' hx'D
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hy.cauchySeq (δ / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : dist (A n x) (A n x') ≤ dist x x' := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hb n _
  have h2 := hN n hn
  have h3 : dist (A N x) (A N x') ≤ dist x x' := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hb N _
  calc dist (A n x) (A N x) ≤ dist (A n x) (A n x') + dist (A n x') (A N x') + dist (A N x') (A N x) :=
        dist_triangle4 _ _ _ _
    _ < δ / 3 + δ / 3 + δ / 3 := by
        rw [dist_comm (A N x') (A N x)] at *
        have := dist_comm (A N x) (A N x')
        linarith
    _ = δ := by ring

end LimitOps

section PolarExist
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
open HilbertCLTAux

/-- Density of `ran S + ker S` for a symmetric operator. -/
lemma dense_range_add_ker {S : H →L[ℝ] H} (hS : IsPSDOp S) :
    Dense ((LinearMap.range (S : H →ₗ[ℝ] H) ⊔ LinearMap.ker (S : H →ₗ[ℝ] H) : Submodule ℝ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro x hx
  have h1 : ∀ y, inner ℝ x (S y) = 0 := fun y => by
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal _ _).1 hx _ (Submodule.mem_sup_left ⟨y, rfl⟩)
  have hSx : S x = 0 := by
    apply ext_inner_right ℝ
    intro y
    rw [hS.symm, h1 y, inner_zero_left]
  have := (Submodule.mem_orthogonal _ _).1 hx x (Submodule.mem_sup_right (by simpa using hSx))
  exact inner_self_eq_zero.1 (by rw [real_inner_comm]; exact this)

end PolarExist

end PolarAbs
end PolarOps
end FragP1

section FragP2
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
section PolarExist2
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
open HilbertCLTAux

lemma resolvent_S_apply {S : H →L[ℝ] H} (hS : IsPSDOp S) (n : ℕ) (y : H) :
    resolvent S n (S y) = y - epsn n • resolvent S n y := by
  have := resolvent_left hS n y
  rw [map_add, map_smul] at this
  exact eq_sub_of_add_eq this

lemma S_resolvent_apply {S : H →L[ℝ] H} (hS : IsPSDOp S) (n : ℕ) (y : H) :
    S (resolvent S n y) = y - epsn n • resolvent S n y := by
  exact eq_sub_of_add_eq (resolvent_right hS n y)

theorem exists_polar {S : H →L[ℝ] H} (hS : IsPSDOp S) (T : H →L[ℝ] F)
    (hT : ∀ x, ‖T x‖ = ‖S x‖) :
    ∃ (U : H →L[ℝ] F) (Q : H →L[ℝ] H),
      (∀ x, Tendsto (fun n => T (resolvent S n x)) atTop (𝓝 (U x))) ∧
      (∀ x, Tendsto (fun n => S (resolvent S n x)) atTop (𝓝 (Q x))) ∧
      (∀ x y, inner ℝ (Q x) y = inner ℝ x (Q y)) ∧ (∀ x, Q (Q x) = Q x) ∧
      (∀ x, Q (S x) = S x) ∧ (∀ x, U (S x) = T x) ∧ (∀ x, ‖U x‖ = ‖Q x‖) := by
  let Qn : ℕ → H →L[ℝ] H := fun n => S ∘L resolvent S n
  let Un : ℕ → H →L[ℝ] F := fun n => T ∘L resolvent S n
  have hQn : ∀ n x, Qn n x = S (resolvent S n x) := fun n x => rfl
  have hUn : ∀ n x, Un n x = T (resolvent S n x) := fun n x => rfl
  have hQb : ∀ n x, ‖Qn n x‖ ≤ ‖x‖ := fun n x => norm_S_resolvent_le hS n x
  have hUb : ∀ n x, ‖Un n x‖ ≤ ‖x‖ := fun n x => by
    rw [hUn, hT]; exact norm_S_resolvent_le hS n x
  have herr : ∀ y, Tendsto (fun n => epsn n • S (resolvent S n y)) atTop (𝓝 0) := fun y => by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using tendsto_epsn.mul_const ‖y‖)
    rw [norm_smul, Real.norm_of_nonneg (epsn_pos n).le]
    exact mul_le_mul_of_nonneg_left (norm_S_resolvent_le hS n y) (epsn_pos n).le
  have key : ∀ y w, S w = 0 → Tendsto (fun n => Qn n (S y + w)) atTop (𝓝 (S y)) ∧
      Tendsto (fun n => Un n (S y + w)) atTop (𝓝 (T y)) := by
    intro y w hw
    have hTw : T w = 0 := by
      have := hT w; rw [hw, norm_zero] at this; exact norm_eq_zero.1 this
    have eQ : ∀ n, Qn n (S y + w) = S y - epsn n • S (resolvent S n y) := fun n => by
      rw [hQn, map_add, map_add, resolvent_of_ker hS n hw, resolvent_S_apply hS n y, map_smul,
        hw, smul_zero, add_zero, map_sub, map_smul]
    have eU : ∀ n, Un n (S y + w) = T y - epsn n • T (resolvent S n y) := fun n => by
      rw [hUn, map_add, resolvent_of_ker hS n hw, resolvent_S_apply hS n y, map_add, map_smul,
        hTw, smul_zero, add_zero, map_sub, map_smul]
    refine ⟨?_, ?_⟩
    · simp_rw [eQ]
      simpa using (tendsto_const_nhds (x := S y)).sub (herr y)
    · simp_rw [eU]
      have : Tendsto (fun n => epsn n • T (resolvent S n y)) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
          (by simpa using tendsto_epsn.mul_const ‖y‖)
        rw [norm_smul, Real.norm_of_nonneg (epsn_pos n).le, hT]
        exact mul_le_mul_of_nonneg_left (norm_S_resolvent_le hS n y) (epsn_pos n).le
      simpa using (tendsto_const_nhds (x := T y)).sub this
  have hD := dense_range_add_ker hS
  have hmem : ∀ x ∈ ((LinearMap.range (S : H →ₗ[ℝ] H) ⊔ LinearMap.ker (S : H →ₗ[ℝ] H) :
      Submodule ℝ H) : Set H), ∃ y w, S w = 0 ∧ x = S y + w := by
    intro x hx
    obtain ⟨a, ⟨y, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨y, b, by simpa using hb, rfl⟩
  have hQc := tendsto_of_dense Qn hQb hD (fun x hx => by
    obtain ⟨y, w, hw, rfl⟩ := hmem x hx
    exact ⟨_, (key y w hw).1⟩)
  have hUc := tendsto_of_dense Un hUb hD (fun x hx => by
    obtain ⟨y, w, hw, rfl⟩ := hmem x hx
    exact ⟨_, (key y w hw).2⟩)
  obtain ⟨Q, hQ⟩ := exists_clm_of_tendsto Qn hQb hQc
  obtain ⟨U, hU⟩ := exists_clm_of_tendsto Un hUb hUc
  have hQS : ∀ x, Q (S x) = S x := fun x => by
    have := (key x 0 (by simp)).1
    simp only [add_zero] at this
    exact tendsto_nhds_unique (hQ _) this
  have hUS : ∀ x, U (S x) = T x := fun x => by
    have := (key x 0 (by simp)).2
    simp only [add_zero] at this
    exact tendsto_nhds_unique (hU _) this
  refine ⟨U, Q, hU, hQ, ?_, ?_, hQS, hUS, ?_⟩
  · intro x y
    have h1 := Filter.Tendsto.inner (𝕜 := ℝ) (hQ x) (tendsto_const_nhds (x := y))
    have h2 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := x)) (hQ y)
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    show inner ℝ x (S (resolvent S n y)) = inner ℝ (S (resolvent S n x)) y
    rw [hS.symm, resolvent_symm hS, resolvent_S_apply hS, S_resolvent_apply hS]
  · intro x
    have h1 := (Q.continuous.tendsto _).comp (hQ x)
    have h2 : (fun n => Q (Qn n x)) = fun n => Qn n x := funext fun n => by
      rw [hQn]; exact hQS _
    rw [Function.comp_def, h2] at h1
    exact tendsto_nhds_unique h1 (hQ x)
  · intro x
    refine tendsto_nhds_unique (hU x).norm ((hQ x).norm.congr fun n => ?_)
    rw [hUn, hQn, hT]

end PolarExist2
end FragP2

section FragP3
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
section ResolventMeas
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
open HilbertCLTAux

/-- Neumann-series data for `S + ε` when `⟪Sx,x⟫ ≤ c₀‖x‖²`. -/
lemma neumann_aux {S : H →L[ℝ] H} (hS : IsPSDOp S) {c₀ ε : ℝ} (hc₀ : 0 ≤ c₀) (hε : 0 < ε)
    (hb : ∀ x, inner ℝ (S x) x ≤ c₀ * ‖x‖ ^ 2) :
    ‖(1 : H →L[ℝ] H) - (c₀ + ε)⁻¹ • (S + ε • (1 : H →L[ℝ] H))‖ < 1 ∧
    S + ε • (1 : H →L[ℝ] H) =
      (c₀ + ε) • (1 - ((1 : H →L[ℝ] H) - (c₀ + ε)⁻¹ • (S + ε • (1 : H →L[ℝ] H)))) := by
  set c : ℝ := c₀ + ε with hc
  have hcpos : 0 < c := by positivity
  set E : H →L[ℝ] H := 1 - c⁻¹ • (S + ε • (1 : H →L[ℝ] H)) with hE
  have hEapp : ∀ x, E x = x - c⁻¹ • (S x + ε • x) := fun x => by simp [hE]
  have hEinner : ∀ x, inner ℝ (E x) x = ‖x‖ ^ 2 - c⁻¹ * (inner ℝ (S x) x + ε * ‖x‖ ^ 2) := fun x => by
    rw [hEapp, inner_sub_left, inner_smul_left, inner_add_left, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp
  have hEp : IsPSDOp E := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [hEapp, hEapp]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, conj_trivial, hS.symm x y]
    · rw [hEinner]
      have h1 := hb x
      have h2 : c⁻¹ * (inner ℝ (S x) x + ε * ‖x‖ ^ 2) ≤ c⁻¹ * (c * ‖x‖ ^ 2) := by
        gcongr
        rw [hc]; nlinarith
      rw [← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul] at h2
      linarith
  have hm : 0 ≤ 1 - ε / c := by
    rw [sub_nonneg, div_le_one hcpos]; rw [hc]; linarith
  have hEn : ‖E‖ ≤ 1 - ε / c := by
    refine ContinuousLinearMap.opNorm_le_bound _ hm fun x => ?_
    refine hEp.norm_apply_le' hm (fun y => ?_) x
    rw [hEinner]
    have h1 := hS.nonneg y
    have : c⁻¹ * (inner ℝ (S y) y + ε * ‖y‖ ^ 2) ≥ c⁻¹ * (ε * ‖y‖ ^ 2) := by
      gcongr; linarith
    have e : (1 - ε / c) * ‖y‖ ^ 2 = ‖y‖ ^ 2 - c⁻¹ * (ε * ‖y‖ ^ 2) := by field_simp
    linarith
  refine ⟨?_, ?_⟩
  · have : 0 < ε / c := by positivity
    linarith
  · rw [hE, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]

lemma resolvent_eq_neumann {S : H →L[ℝ] H} (hS : IsPSDOp S) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (n : ℕ)
    (hb : ∀ x, inner ℝ (S x) x ≤ c₀ * ‖x‖ ^ 2) :
    resolvent S n = (c₀ + epsn n)⁻¹ •
      Ring.inverse (1 - ((1 : H →L[ℝ] H) - (c₀ + epsn n)⁻¹ • (S + epsn n • (1 : H →L[ℝ] H)))) := by
  obtain ⟨hlt, heq⟩ := neumann_aux hS hc₀ (epsn_pos n) hb
  set c : ℝ := c₀ + epsn n with hc
  have hcpos : 0 < c := by have := epsn_pos n; positivity
  set E : H →L[ℝ] H := 1 - c⁻¹ • (S + epsn n • (1 : H →L[ℝ] H)) with hE
  have h1E : IsUnit (1 - E) := (Units.oneSub E hlt).isUnit
  have hl : Ring.inverse (1 - E) * (1 - E) = 1 := Ring.inverse_mul_cancel _ h1E
  have hr : (1 - E) * Ring.inverse (1 - E) = 1 := Ring.mul_inverse_cancel _ h1E
  have hRl : resolvent S n * (S + epsn n • (1 : H →L[ℝ] H)) = 1 :=
    Ring.inverse_mul_cancel _ (isUnit_add_smul_one hS (epsn_pos n))
  have hR'r : (S + epsn n • (1 : H →L[ℝ] H)) * (c⁻¹ • Ring.inverse (1 - E)) = 1 := by
    rw [heq, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul, hr]
  calc resolvent S n = resolvent S n * ((S + epsn n • (1 : H →L[ℝ] H)) * (c⁻¹ • Ring.inverse (1 - E))) := by
        rw [hR'r, mul_one]
    _ = (resolvent S n * (S + epsn n • (1 : H →L[ℝ] H))) * (c⁻¹ • Ring.inverse (1 - E)) := by rw [mul_assoc]
    _ = _ := by rw [hRl, one_mul]

end ResolventMeas
end FragP3

section FragP4
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
section PolarMeas
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Z : Type*} [MeasurableSpace Z]
open HilbertCLTAux

lemma OpMeas.pow {A : Z → H →L[ℝ] H} (hA : OpMeas A) : ∀ m : ℕ, OpMeas fun z => A z ^ m
  | 0 => by simpa using OpMeas.const (Z := Z) (1 : H →L[ℝ] H)
  | m + 1 => by
      have := OpMeas.mul (OpMeas.pow hA m) hA
      simpa [pow_succ] using this

lemma OpMeas.sum_pow {A : Z → H →L[ℝ] H} (hA : OpMeas A) :
    ∀ N : ℕ, OpMeas fun z => ∑ m ∈ Finset.range N, A z ^ m
  | 0 => by simpa using OpMeas.const (Z := Z) (0 : H →L[ℝ] H)
  | N + 1 => by
      have := OpMeas.add (OpMeas.sum_pow hA N) (OpMeas.pow hA N)
      simpa [Finset.sum_range_succ] using this

lemma OpMeas.resolvent {A : Z → H →L[ℝ] H} (hA : OpMeas A) {c₀ : Z → ℝ} (hc₀ : Measurable c₀)
    (hp : ∀ z, IsPSDOp (A z)) (hc0 : ∀ z, 0 ≤ c₀ z)
    (hb : ∀ z x, inner ℝ (A z x) x ≤ c₀ z * ‖x‖ ^ 2) (n : ℕ) :
    OpMeas fun z => resolvent (A z) n := by
  intro x
  have hcm : Measurable fun z => (c₀ z + epsn n)⁻¹ := (hc₀.add measurable_const).inv
  have hE : OpMeas fun z => (1 : H →L[ℝ] H) - (c₀ z + epsn n)⁻¹ •
      (A z + epsn n • (1 : H →L[ℝ] H)) :=
    OpMeas.sub (OpMeas.const 1) (OpMeas.smul hcm (OpMeas.add hA (OpMeas.const _)))
  have hinv : OpMeas fun z => Ring.inverse (1 - ((1 : H →L[ℝ] H) - (c₀ z + epsn n)⁻¹ •
      (A z + epsn n • (1 : H →L[ℝ] H)))) := by
    intro y
    refine measurable_of_tendsto_metrizable (f := fun N z => (∑ m ∈ Finset.range N,
      ((1 : H →L[ℝ] H) - (c₀ z + epsn n)⁻¹ • (A z + epsn n • (1 : H →L[ℝ] H))) ^ m) y)
      (fun N => (OpMeas.sum_pow hE N) y) (tendsto_pi_nhds.2 fun z => ?_)
    obtain ⟨hlt, -⟩ := neumann_aux (hp z) (hc0 z) (epsn_pos n) (hb z)
    have hs := hasSum_geom_series_inverse _ hlt
    exact ((ContinuousLinearMap.apply ℝ H y).continuous.tendsto _).comp hs.tendsto_sum_nat
  have := OpMeas.smul hcm hinv
  simp_rw [resolvent_eq_neumann (hp _) (hc0 _) n (hb _)]
  exact this x

end PolarMeas
end FragP4

section FragP5
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
section HsAdjoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {κ : Type*}

lemma norm_smulRight_innerSL_le (a : H) :
    ‖(innerSL ℝ a).smulRight (innerSL ℝ a)‖ ≤ ‖a‖ ^ 2 := by
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, sq]

lemma summable_hsCov {Φ : κ → H} (hΦ : Summable fun k => ‖Φ k‖ ^ 2) :
    Summable fun k => (innerSL ℝ (Φ k)).smulRight (innerSL ℝ (Φ k)) := by
  have hc : CompleteSpace (H →L[ℝ] H →L[ℝ] ℝ) := inferInstance
  exact Summable.of_norm_bounded (f := fun k => (innerSL ℝ (Φ k)).smulRight (innerSL ℝ (Φ k))) hΦ
    (fun k => norm_smulRight_innerSL_le _)

lemma hsCovForm_apply {Φ : κ → H} (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (x y : H) :
    hsCovForm Φ x y = ∑' k, inner ℝ (Φ k) x * inner ℝ (Φ k) y := by
  have hs := summable_hsCov hΦ
  have h1 := (ContinuousLinearMap.apply ℝ (H →L[ℝ] ℝ) x).map_tsum hs
  have h2 := (ContinuousLinearMap.apply ℝ ℝ y).map_tsum
    ((ContinuousLinearMap.apply ℝ (H →L[ℝ] ℝ) x).summable hs)
  unfold hsCovForm
  simp only [ContinuousLinearMap.apply_apply] at h1 h2
  rw [h1, h2]
  simp [innerSL_apply_apply, mul_comm]

section lpPart
variable {Φ : κ → H}

lemma memℓp_hsAdjoint (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (x : H) :
    Memℓp (fun k => inner ℝ (Φ k) x) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (hΦ.mul_right (‖x‖ ^ 2))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_inner_le_norm _ _)) 2

/-- The adjoint `Φ^* : H → ℓ²(κ)`, `x ↦ (⟨Φ_k, x⟩)_k`. -/
def hsAdjoint (hΦ : Summable fun k => ‖Φ k‖ ^ 2) : H →L[ℝ] lp (fun _ : κ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun k => inner ℝ (Φ k) x, memℓp_hsAdjoint hΦ x⟩
      map_add' := fun x y => by
        refine lp.ext (funext fun k => ?_)
        exact inner_add_right _ _ _
      map_smul' := fun c x => by
        refine lp.ext (funext fun k => ?_)
        exact inner_smul_right _ _ _ }
    (Real.sqrt (∑' k, ‖Φ k‖ ^ 2))
    (fun x => by
      refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
      have hsq : Real.sqrt (∑' k, ‖Φ k‖ ^ 2) ^ 2 = ∑' k, ‖Φ k‖ ^ 2 :=
        Real.sq_sqrt (tsum_nonneg fun k => by positivity)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow, hsq]
      rw [← tsum_mul_right]
      refine Summable.tsum_le_tsum (fun k => ?_) ((memℓp_hsAdjoint hΦ x).summable (by norm_num) |>.congr
        (fun k => by simp [Real.rpow_two])) (hΦ.mul_right _)
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_inner_le_norm _ _)) 2)

lemma hsAdjoint_apply (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (x : H) (k : κ) :
    hsAdjoint hΦ x k = inner ℝ (Φ k) x := rfl

lemma inner_hsAdjoint (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (x y : H) :
    inner ℝ (hsAdjoint hΦ x) (hsAdjoint hΦ y) = hsCovForm Φ x y := by
  rw [lp.inner_eq_tsum, hsCovForm_apply hΦ]
  refine tsum_congr fun k => ?_
  simp [hsAdjoint_apply, mul_comm]

lemma norm_hsAdjoint_sq (hΦ : Summable fun k => ‖Φ k‖ ^ 2) (x : H) :
    ‖hsAdjoint hΦ x‖ ^ 2 = hsCovForm Φ x x := by
  rw [← real_inner_self_eq_norm_sq, inner_hsAdjoint]

end lpPart

end HsAdjoint
end FragP5

section FragP6
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
section PolarCoords
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ]
open HilbertCLTAux

section Form
variable {Φ : κ → H} (hΦ : Summable fun k => ‖Φ k‖ ^ 2)
include hΦ

lemma hsCovForm_symm' (x y : H) : hsCovForm Φ x y = hsCovForm Φ y x := by
  rw [hsCovForm_apply hΦ, hsCovForm_apply hΦ]
  exact tsum_congr fun k => mul_comm _ _

lemma hsCovForm_nonneg' (x : H) : 0 ≤ hsCovForm Φ x x := by
  rw [hsCovForm_apply hΦ]
  exact tsum_nonneg fun k => mul_self_nonneg _

lemma hsCovForm_le' (x : H) : hsCovForm Φ x x ≤ (∑' k, ‖Φ k‖ ^ 2) * ‖x‖ ^ 2 := by
  rw [hsCovForm_apply hΦ, ← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ (hΦ.mul_right _)
  · rw [← mul_pow]
    have := norm_inner_le_norm (𝕜 := ℝ) (Φ k) x
    have h2 : inner ℝ (Φ k) x * inner ℝ (Φ k) x = ‖inner ℝ (Φ k) x‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs, sq]
    rw [h2]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  · have := (memℓp_hsAdjoint hΦ x).summable (by norm_num)
    refine this.congr fun k => ?_
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, sq]

lemma isPSDOp_formOp_hsCov : IsPSDOp (formOp (hsCovForm Φ)) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [inner_formOp, real_inner_comm, inner_formOp, hsCovForm_symm' hΦ]
  · rw [inner_formOp]; exact hsCovForm_nonneg' hΦ x

end Form

lemma hasSum_sumElim {α β : Type*} {g : α → ℝ} {h : β → ℝ} {a b : ℝ} (hg : HasSum g a)
    (hh : HasSum h b) : HasSum (Sum.elim g h) (a + b) :=
  HasSum.sum (f := Sum.elim g h) hg hh

set_option maxHeartbeats 1000000 in
theorem exists_polar_coords {Z : Type*} [MeasurableSpace Z] {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ H) (Φ : Z → κ → H) (hΦm : ∀ k, Measurable fun z => Φ z k)
    (hΦs : ∀ z, Summable fun k => ‖Φ z k‖ ^ 2) :
    ∃ (S : Z → H →L[ℝ] H) (coord : Z → H → κ ⊕ ι → ℝ),
      OpMeas S ∧ (∀ z, IsSqrtOfForm (S z) (hsCovForm (Φ z))) ∧
      (∀ x a, Measurable fun z => coord z x a) ∧
      (∀ z x, HasSum (fun a => coord z x a ^ 2) (‖x‖ ^ 2)) ∧
      (∀ z x y a, coord z (x + y) a = coord z x a + coord z y a) ∧
      (∀ z (c : ℝ) x a, coord z (c • x) a = c * coord z x a) ∧
      (∀ z x k, coord z (S z x) (Sum.inl k) = inner ℝ (Φ z k) x) ∧
      (∀ z x l, coord z (S z x) (Sum.inr l) = 0) := by
  classical
  set A : Z → H →L[ℝ] H := fun z => formOp (hsCovForm (Φ z)) with hA
  have hAp : ∀ z, IsPSDOp (A z) := fun z => isPSDOp_formOp_hsCov (hΦs z)
  have hAinner : ∀ z x y, inner ℝ (A z x) y = ∑' k, inner ℝ (Φ z k) x * inner ℝ (Φ z k) y :=
    fun z x y => by rw [hA]; dsimp only; rw [inner_formOp, hsCovForm_apply (hΦs z)]
  have hAm : OpMeas A := by
    intro x
    refine measurable_of_inner_basis e (fun i => ?_)
    have : (fun z => inner ℝ (e i) (A z x)) =
        fun z => ∑' k, inner ℝ (Φ z k) x * inner ℝ (Φ z k) (e i) := by
      funext z; rw [real_inner_comm, hAinner]
    rw [this]
    exact Measurable.tsum fun k => ((hΦm k).inner measurable_const).mul
      ((hΦm k).inner measurable_const)
  set c : Z → ℝ := fun z => 1 + ∑' k, ‖Φ z k‖ ^ 2 with hc
  have hcm : Measurable c := measurable_const.add (Measurable.tsum fun k => (hΦm k).norm.pow_const 2)
  have hcpos : ∀ z, 0 < c z := fun z => by
    have : 0 ≤ ∑' k, ‖Φ z k‖ ^ 2 := tsum_nonneg fun k => sq_nonneg _
    rw [hc]; dsimp only; linarith
  have hAc : ∀ z x, inner ℝ (A z x) x ≤ c z * ‖x‖ ^ 2 := fun z x => by
    rw [hA]; dsimp only; rw [inner_formOp]
    have := hsCovForm_le' (hΦs z) x
    have h2 : (∑' k, ‖Φ z k‖ ^ 2) * ‖x‖ ^ 2 ≤ c z * ‖x‖ ^ 2 := by
      rw [hc]; dsimp only; nlinarith [sq_nonneg ‖x‖]
    linarith
  set S : Z → H →L[ℝ] H := fun z => sqrtOp (c z) (A z) with hS
  have hSm : OpMeas S := OpMeas.sqrtOp hAm hcm hAp hcpos hAc
  have hSspec : ∀ z, IsPSDOp (S z) ∧ S z * S z = A z := fun z =>
    sqrtOp_spec (hAp z) (hcpos z) (hAc z)
  have hSsq : ∀ z x y, inner ℝ (S z x) (S z y) = hsCovForm (Φ z) x y := fun z x y => by
    rw [(hSspec z).1.symm x (S z y)]
    have : S z (S z y) = A z y := by
      have := congrArg (fun T : H →L[ℝ] H => T y) (hSspec z).2
      simpa using this
    rw [this, real_inner_comm, hA]; dsimp only
    rw [inner_formOp, hsCovForm_symm' (hΦs z)]
  have hS0 : ∀ z x, inner ℝ (S z x) x ≤ Real.sqrt (c z) * ‖x‖ ^ 2 := fun z x => by
    have h1 : ‖S z x‖ ≤ Real.sqrt (c z) * ‖x‖ := by
      have h2 : ‖S z x‖ ^ 2 ≤ (Real.sqrt (c z) * ‖x‖) ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hSsq z x x, mul_pow, Real.sq_sqrt (hcpos z).le]
        have := hsCovForm_le' (hΦs z) x
        have h3 : (∑' k, ‖Φ z k‖ ^ 2) * ‖x‖ ^ 2 ≤ c z * ‖x‖ ^ 2 := by
          rw [hc]; dsimp only; nlinarith [sq_nonneg ‖x‖]
        linarith
      exact le_of_sq_le_sq h2 (by positivity)
    calc inner ℝ (S z x) x ≤ ‖S z x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (Real.sqrt (c z) * ‖x‖) * ‖x‖ := by gcongr
      _ = Real.sqrt (c z) * ‖x‖ ^ 2 := by ring
  have hR : ∀ n, OpMeas fun z => resolvent (S z) n := fun n =>
    OpMeas.resolvent hSm hcm.sqrt (fun z => (hSspec z).1) (fun z => Real.sqrt_nonneg _) hS0 n
  have hT : ∀ z x, ‖hsAdjoint (hΦs z) x‖ = ‖S z x‖ := fun z x => by
    have h1 : ‖hsAdjoint (hΦs z) x‖ ^ 2 = ‖S z x‖ ^ 2 := by
      rw [norm_hsAdjoint_sq, ← real_inner_self_eq_norm_sq, hSsq]
    exact le_antisymm (le_of_sq_le_sq h1.le (norm_nonneg _)) (le_of_sq_le_sq h1.ge (norm_nonneg _))
  choose U Q hU hQ hQsymm hQQ hQS hUS hUQ using fun z =>
    exists_polar (hSspec z).1 (hsAdjoint (hΦs z)) (hT z)
  have hUk : ∀ x k, Measurable fun z => (U z x) k := fun x k => by
    refine measurable_of_tendsto_metrizable (f := fun n z =>
      inner ℝ (Φ z k) (resolvent (S z) n x)) (fun n => (hΦm k).inner (hR n x))
      (tendsto_pi_nhds.2 fun z => ?_)
    exact ((lp.lipschitzWith_one_eval (E := fun _ : κ => ℝ) 2 k).continuous.tendsto _).comp (hU z x)
  have hQm : ∀ x, Measurable fun z => Q z x := fun x =>
    measurable_of_tendsto_metrizable (f := fun n z => S z (resolvent (S z) n x))
      (fun n => OpMeas.apply hSm (hR n x)) (tendsto_pi_nhds.2 fun z => hQ z x)
  refine ⟨S, fun z x => Sum.elim (fun k => (U z x) k) (fun l => inner ℝ (x - Q z x) (e l)), hSm,
    fun z => ⟨(hSspec z).1.symm, (hSspec z).1.nonneg, hSsq z⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x a
    rcases a with k | l
    · exact hUk x k
    · exact (measurable_const.sub (hQm x)).inner measurable_const
  · intro z x
    have h1 : HasSum (fun k : κ => ((U z x) k) ^ 2) (‖U z x‖ ^ 2) := by
      have := lp.hasSum_norm (E := fun _ : κ => ℝ) (p := 2) (by norm_num) (U z x)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at this
      exact this
    have h2 : HasSum (fun l : ι => inner ℝ (x - Q z x) (e l) ^ 2) (‖x - Q z x‖ ^ 2) := by
      have := e.hasSum_inner_mul_inner (x - Q z x) (x - Q z x)
      rw [real_inner_self_eq_norm_sq] at this
      convert this using 2 with l
      rw [sq, real_inner_comm (x - Q z x) (e l)]
    have h3 : HasSum (fun a : κ ⊕ ι => (Sum.elim (fun k => (U z x) k)
        (fun l => inner ℝ (x - Q z x) (e l)) a) ^ 2) (‖U z x‖ ^ 2 + ‖x - Q z x‖ ^ 2) := by
      have := hasSum_sumElim h1 h2
      convert this using 1
      funext a; rcases a with k | l <;> rfl
    have h4 : ‖U z x‖ ^ 2 + ‖x - Q z x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [hUQ z x]
      have e1 : inner ℝ (Q z x) (x - Q z x) = 0 := by
        rw [inner_sub_right, ← hQQ z x, hQsymm z (Q z x) x, hQQ z x]
        simp
      have := norm_add_sq_eq_norm_sq_add_norm_sq_real e1
      rw [add_sub_cancel] at this
      rw [sq, sq, sq]; exact this.symm
    rw [h4] at h3
    exact h3
  · intro z x y a
    rcases a with k | l
    · simp
    · simp only [Sum.elim_inr, map_add, inner_sub_left, inner_add_left]; ring
  · intro z c x a
    rcases a with k | l
    · simp
    · simp only [Sum.elim_inr, map_smul, inner_sub_left, inner_smul_left, conj_trivial]; ring
  · intro z x k
    simp [hUS z x, hsAdjoint_apply]
  · intro z x l
    simp [hQS z x]

end PolarCoords
end FragP6

section FragPS1
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix
section PSCore
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The vectors `h_i = ∑_a v_i(a) ε_a` for an orthonormal basis `v` of `ℝ^A`. -/
def rotVec (v : OrthonormalBasis A ℝ (EuclideanSpace ℝ A)) (ε : A → H) (i : A) : H :=
  ∑ a, v i a • ε a

lemma inner_rotVec_left (v : OrthonormalBasis A ℝ (EuclideanSpace ℝ A)) (ε : A → H) (i : A)
    (u : H) : inner ℝ (rotVec v ε i) u = ∑ a, v i a * inner ℝ (ε a) u := by
  simp [rotVec, sum_inner, inner_smul_left]

lemma inner_rotVec_right (v : OrthonormalBasis A ℝ (EuclideanSpace ℝ A)) (ε : A → H) (i : A)
    (u : H) : inner ℝ u (rotVec v ε i) = ∑ a, v i a * inner ℝ u (ε a) := by
  simp [rotVec, inner_sum, inner_smul_right]

lemma sum_sq_inner_rotVec (v : OrthonormalBasis A ℝ (EuclideanSpace ℝ A)) (ε : A → H) (u : H) :
    ∑ i, inner ℝ (rotVec v ε i) u ^ 2 = ∑ a, inner ℝ (ε a) u ^ 2 := by
  set c : EuclideanSpace ℝ A := WithLp.toLp 2 (fun a => inner ℝ (ε a) u) with hc
  have h := v.sum_sq_norm_inner_right c
  have h1 : ∀ i, inner ℝ (v i) c = ∑ a, v i a * inner ℝ (ε a) u := fun i => by
    simp [hc, PiLp.inner_apply, mul_comm]
  have h2 : ‖c‖ ^ 2 = ∑ a, inner ℝ (ε a) u ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [hc]
  rw [← h2, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_rotVec_left, ← h1, Real.norm_eq_abs, sq_abs]


lemma orthonormal_rotVec (v : OrthonormalBasis A ℝ (EuclideanSpace ℝ A)) {ε : A → H}
    (hε : Orthonormal ℝ ε) : Orthonormal ℝ (rotVec v ε) := by
  rw [orthonormal_iff_ite]
  intro i l
  rw [inner_rotVec_left]
  have h1 : ∀ a, inner ℝ (ε a) (rotVec v ε l) = v l a := fun a => by
    rw [inner_rotVec_right]
    simp [orthonormal_iff_ite.1 hε, Finset.sum_ite_eq]
  simp_rw [h1]
  have := orthonormal_iff_ite.1 v.orthonormal i l
  rw [← this]
  simp [PiLp.inner_apply, mul_comm]

lemma ps_core (ε : A → H) (hε : Orthonormal ℝ ε) (D Y : H →L[ℝ] H)
    (hDs : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y))
    (hYs : ∀ x y, inner ℝ (Y x) y = inner ℝ x (Y y))
    (hYD : ∀ x, |inner ℝ (D x) x| ≤ inner ℝ (Y x) x) (T K : ℝ)
    (hT : ∀ (h : A → H), Orthonormal ℝ h → ∀ s : A → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
        ∑ i, s i * inner ℝ (D (h i)) (Y (h i)) ≤ T)
    (hK : ∀ (h : A → H), Orthonormal ℝ h → ∑ i, ‖Y (h i)‖ ^ 2 ≤ K) :
    ∃ v : OrthonormalBasis A ℝ (EuclideanSpace ℝ A),
      ∑ a, ∑ b, inner ℝ (D (ε a)) (ε b) ^ 2 ≤ T +
        Real.sqrt (∑ i, ‖D (rotVec v ε i) - ∑ b, inner ℝ (D (rotVec v ε i)) (ε b) • ε b‖ ^ 2) *
          Real.sqrt K := by
  set M : Matrix A A ℝ := Matrix.of fun a b => inner ℝ (D (ε a)) (ε b) with hMdef
  have hM : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [hMdef, Matrix.of_apply, star_trivial]
    rw [hDs, real_inner_comm]
  set v := hM.eigenvectorBasis with hv
  set d := hM.eigenvalues with hd
  refine ⟨v, ?_⟩
  set h := rotVec v ε with hh
  have hon : Orthonormal ℝ h := orthonormal_rotVec v hε
  have hDh : ∀ i b, inner ℝ (D (h i)) (ε b) = d i * v i b := fun i b => by
    have := congrFun (hM.mulVec_eigenvectorBasis i) b
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [hDs, hh, inner_rotVec_left, ← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hMdef, Matrix.of_apply]
    rw [real_inner_comm (D (ε b)) (ε a), hDs, real_inner_comm]
    ring
  have hvsq : ∀ i, ∑ b, v i b ^ 2 = 1 := fun i => by
    have h1 := v.orthonormal.1 i
    have h2 : ‖v i‖ ^ 2 = ∑ b, v i b ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]; simp
    rw [← h2, h1]; norm_num
  have hPD : ∀ i, ∑ b, inner ℝ (D (h i)) (ε b) • ε b = d i • h i := fun i => by
    simp_rw [hDh, mul_smul]
    rw [← Finset.smul_sum, hh, rotVec]
  have hDhh : ∀ i, inner ℝ (D (h i)) (h i) = d i := fun i => by
    rw [hh, inner_rotVec_right]
    simp_rw [← hh, hDh]
    have : ∑ b, v i b * (d i * v i b) = d i * ∑ b, v i b ^ 2 := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
    rw [this, hvsq]; ring
  set w : A → H := fun i => D (h i) - d i • h i with hw
  have hwdef : ∀ i, D (h i) - ∑ b, inner ℝ (D (h i)) (ε b) • ε b = w i := fun i => by
    rw [hPD]
  set s : A → ℝ := fun i => if 0 ≤ d i then 1 else -1 with hs
  have hs1 : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    by_cases hi : 0 ≤ d i <;> simp [hs, hi]
  have hsd : ∀ i, s i * d i = |d i| := fun i => by
    by_cases hi : 0 ≤ d i
    · simp [hs, hi, abs_of_nonneg hi]
    · simp [hs, hi, abs_of_neg (not_le.1 hi)]
  have hyh : ∀ i, |d i| ≤ inner ℝ (Y (h i)) (h i) := fun i => by
    have := hYD (h i); rwa [hDhh] at this
  have hkey : ∀ i, d i ^ 2 - ‖w i‖ * ‖Y (h i)‖ ≤ s i * inner ℝ (D (h i)) (Y (h i)) := fun i => by
    have e1 : inner ℝ (D (h i)) (Y (h i)) = d i * inner ℝ (h i) (Y (h i)) + inner ℝ (w i) (Y (h i)) := by
      rw [hw]; simp only [inner_sub_left, inner_smul_left, conj_trivial]; ring
    have e2 : inner ℝ (h i) (Y (h i)) = inner ℝ (Y (h i)) (h i) := real_inner_comm _ _
    have e3 : |inner ℝ (w i) (Y (h i))| ≤ ‖w i‖ * ‖Y (h i)‖ := abs_real_inner_le_norm _ _
    have e4 : s i * inner ℝ (w i) (Y (h i)) ≥ -(‖w i‖ * ‖Y (h i)‖) := by
      rcases hs1 i with h1 | h1 <;> rw [h1] <;> [skip; skip] <;> nlinarith [abs_le.1 e3]
    rw [e1, mul_add, ← mul_assoc, hsd, e2]
    have e5 : |d i| * |d i| ≤ |d i| * inner ℝ (Y (h i)) (h i) :=
      mul_le_mul_of_nonneg_left (hyh i) (abs_nonneg _)
    rw [← sq, sq_abs] at e5
    nlinarith
  have hsum_d : ∑ i, d i ^ 2 = ∑ a, ∑ b, inner ℝ (D (ε a)) (ε b) ^ 2 := by
    have h1 : ∀ i, d i ^ 2 = ∑ b, inner ℝ (h i) (D (ε b)) ^ 2 := fun i => by
      have : ∀ b, inner ℝ (h i) (D (ε b)) = d i * v i b := fun b => by
        rw [← hDs, hDh]
      simp_rw [this, mul_pow, ← Finset.mul_sum, hvsq, mul_one]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have := sum_sq_inner_rotVec v ε (D (ε b))
    rw [← hh] at this
    simp_rw [real_inner_comm (D (ε b))] at this ⊢
    rw [this]
  have hT' := hT h hon s hs1
  have hK' := hK h hon
  have hCS : ∑ i, ‖w i‖ * ‖Y (h i)‖ ≤ Real.sqrt (∑ i, ‖w i‖ ^ 2) * Real.sqrt K := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    gcongr
  simp_rw [hwdef]
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hkey i
  rw [Finset.sum_sub_distrib] at this
  linarith

end PSCore
end FragPS1

section FragPS2
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix
section PSLimit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H]
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma signed_sum_le_traceNormForm {Z : H →L[ℝ] H →L[ℝ] ℝ}
    (hb : BddAbove (Set.range fun p : OrthonormalPairs H => ∑ i, |Z (p.1.2.1 i) (p.1.2.2 i)|))
    (h : A → H) (hon : Orthonormal ℝ h) (s : A → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    ∑ i, s i * Z (h i) (h i) ≤ traceNormForm Z := by
  set f : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm with hf
  have hon1 : Orthonormal ℝ (fun i : Fin (Fintype.card A) => h (f i)) :=
    hon.comp f f.injective
  have hon2 : Orthonormal ℝ (fun i : Fin (Fintype.card A) => s (f i) • h (f i)) := by
    rw [orthonormal_iff_ite] at hon1 ⊢
    intro i j
    rw [inner_smul_left, inner_smul_right, conj_trivial, ← mul_assoc]
    have := hon1 i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at this ⊢
      rw [this]
      rcases hs (f i) with h1 | h1 <;> rw [h1] <;> norm_num
    · rw [if_neg hij] at this ⊢
      rw [this, mul_zero]
  let p : OrthonormalPairs H := ⟨⟨Fintype.card A, fun i => h (f i), fun i => s (f i) • h (f i)⟩,
    hon1, hon2⟩
  have h1 := pairSum_le_traceNormForm hb p
  refine le_trans ?_ h1
  simp only [p, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul]
  rw [Fintype.sum_equiv f (fun i => |s (f i)| * |Z (h (f i)) (h (f i))|)
    (fun a => |s a| * |Z (h a) (h a)|) (fun i => rfl)]
  refine Finset.sum_le_sum fun a _ => ?_
  rcases hs a with h1 | h1 <;> simp [h1] <;> [exact le_abs_self _; exact neg_le_abs _]

section Parseval
variable {ι : Type*} (e : HilbertBasis ι ℝ H)

lemma hasSum_inner_sq (x : H) : HasSum (fun n => inner ℝ x (e n) ^ 2) (‖x‖ ^ 2) := by
  have := e.hasSum_inner_mul_inner x x
  rw [real_inner_self_eq_norm_sq] at this
  convert this using 2 with n
  rw [sq, real_inner_comm x (e n)]

lemma sum_norm_sq_swap {L : H →L[ℝ] H} (hL : ∀ x y, inner ℝ (L x) y = inner ℝ x (L y))
    (h : A → H) :
    ∑ i, ‖L (h i)‖ ^ 2 = ∑' n, ∑ i, inner ℝ (h i) (L (e n)) ^ 2 := by
  have h1 : ∀ i, HasSum (fun n => inner ℝ (h i) (L (e n)) ^ 2) (‖L (h i)‖ ^ 2) := fun i => by
    convert hasSum_inner_sq e (L (h i)) using 2 with n
    rw [real_inner_comm, hL, real_inner_comm]
  rw [Summable.tsum_finsetSum (fun i _ => (h1 i).summable)]
  exact Finset.sum_congr rfl fun i _ => (h1 i).tsum_eq.symm

end Parseval

section PSMain
variable {ι : Type*} (e : HilbertBasis ι ℝ H)

lemma norm_sub_sum_sq {B : Type*} [Fintype B] [DecidableEq B] {ε : B → H} (hε : Orthonormal ℝ ε) (u : H) :
    ‖u - ∑ b, inner ℝ u (ε b) • ε b‖ ^ 2 = ‖u‖ ^ 2 - ∑ b, inner ℝ u (ε b) ^ 2 := by
  have h1 : inner ℝ u (∑ b, inner ℝ u (ε b) • ε b) = ∑ b, inner ℝ u (ε b) ^ 2 := by
    simp only [inner_sum, inner_smul_right, sq]
  have h2 : ‖∑ b, inner ℝ u (ε b) • ε b‖ ^ 2 = ∑ b, inner ℝ u (ε b) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    set c : B → ℝ := fun b => inner ℝ u (ε b) with hc
    have : inner ℝ (∑ a, c a • ε a) (∑ b, c b • ε b) = ∑ a, ∑ b, c a * c b * inner ℝ (ε a) (ε b) := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [inner_smul_right]; simp only [conj_trivial]; ring
    rw [this]
    simp only [orthonormal_iff_ite.1 hε, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [hc, sq]
  rw [norm_sub_sq_real, h1, h2]; ring

/-- Powers–Størmer inequality `‖√C - √C'‖²_{𝔖₂} ≤ ‖C - C'‖_{𝔖₁}`, in the form needed:
for square roots `S, S'` of trace-class forms `C, C'`,
`∑_j ‖(S - S') e_j‖² ≤ ‖C - C'‖_{𝔖₁}`. -/
theorem powers_stormer {S S' : H →L[ℝ] H} {C C' : H →L[ℝ] H →L[ℝ] ℝ}
    (hS : IsSqrtOfForm S C) (hS' : IsSqrtOfForm S' C') (hC : IsTraceClassCov C)
    (hC' : IsTraceClassCov C') (hCe : Summable fun i => C (e i) (e i))
    (hCe' : Summable fun i => C' (e i) (e i)) :
    Summable (fun j => ‖(S - S') (e j)‖ ^ 2) ∧
      ∑' j, ‖(S - S') (e j)‖ ^ 2 ≤ traceNormForm (C - C') := by
  classical
  set D : H →L[ℝ] H := S - S' with hD
  set Y : H →L[ℝ] H := S + S' with hY
  have hDs : ∀ x y, inner ℝ (D x) y = inner ℝ x (D y) := fun x y => by
    simp only [hD, ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, hS.symm, hS'.symm]
  have hYs : ∀ x y, inner ℝ (Y x) y = inner ℝ x (Y y) := fun x y => by
    simp only [hY, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, hS.symm, hS'.symm]
  have hYD : ∀ x, |inner ℝ (D x) x| ≤ inner ℝ (Y x) x := fun x => by
    have h1 := hS.nonneg x
    have h2 := hS'.nonneg x
    simp only [hD, hY, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, inner_sub_left,
      inner_add_left]
    rw [abs_le]; constructor <;> linarith
  -- the form `Z = C - C'` along the diagonal
  have hZ : ∀ u, (C - C') u u = inner ℝ (D u) (Y u) := fun u => by
    have h1 := hS.sq u u
    have h2 := hS'.sq u u
    simp only [hD, hY, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, inner_sub_left,
      inner_add_right, inner_add_left, ContinuousLinearMap.coe_sub', Pi.sub_apply]
    rw [real_inner_comm (S' u) (S u)] at *
    rw [← h1, ← h2]
    ring
  have hbdd := bddAbove_pairSum_sub hC hC'
  set T : ℝ := traceNormForm (C - C') with hT
  have hTbound : ∀ (J : Finset ι) (h : J → H), Orthonormal ℝ h →
      ∀ s : J → ℝ, (∀ i, s i = 1 ∨ s i = -1) →
        ∑ i, s i * inner ℝ (D (h i)) (Y (h i)) ≤ T := by
    intro J h hon s hs
    have := signed_sum_le_traceNormForm hbdd h hon s hs
    simpa only [hZ] using this
  have hSn : ∀ n, ‖S (e n)‖ ^ 2 = C (e n) (e n) := fun n => by
    rw [← real_inner_self_eq_norm_sq]; exact hS.sq _ _
  have hSn' : ∀ n, ‖S' (e n)‖ ^ 2 = C' (e n) (e n) := fun n => by
    rw [← real_inner_self_eq_norm_sq]; exact hS'.sq _ _
  have hsq2 : ∀ a b : H, ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := fun a b => by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2, sq_nonneg (‖a‖ - ‖b‖)]
  have hbase : Summable fun n => 2 * C (e n) (e n) + 2 * C' (e n) (e n) :=
    (hCe.mul_left 2).add (hCe'.mul_left 2)
  have hDsum : Summable fun n => ‖D (e n)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
    have := hsq2 (S (e n)) (-S' (e n))
    simp only [norm_neg] at this
    simp only [hD, ContinuousLinearMap.sub_apply, sub_eq_add_neg]
    rw [← hSn, ← hSn']; exact this
  have hYsum : Summable fun n => ‖Y (e n)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
    have := hsq2 (S (e n)) (S' (e n))
    simp only [hY, ContinuousLinearMap.add_apply]
    rw [← hSn, ← hSn']; exact this
  set K : ℝ := ∑' n, ‖Y (e n)‖ ^ 2 with hKdef
  have hK : ∀ (J : Finset ι) (h : J → H), Orthonormal ℝ h → ∑ i, ‖Y (h i)‖ ^ 2 ≤ K := by
    intro J h hon
    rw [sum_norm_sq_swap e hYs h]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ hYsum
    · have := hon.sum_inner_products_le (s := Finset.univ) (Y (e n))
      simpa only [Real.norm_eq_abs, sq_abs] using this
    · refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun i _ => sq_nonneg _)
        (fun n => ?_) hYsum
      have := hon.sum_inner_products_le (s := Finset.univ) (Y (e n))
      simpa only [Real.norm_eq_abs, sq_abs] using this
  -- the finite-dimensional step
  have hfin : ∀ J : Finset ι,
      (∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2) ≤ ∑ a ∈ J, ‖D (e a)‖ ^ 2 ∧
      ∑ a ∈ J, ‖D (e a)‖ ^ 2 ≤ T + Real.sqrt (∑ a ∈ J, ‖D (e a)‖ ^ 2 -
        ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2) * Real.sqrt K +
        (∑ a ∈ J, ‖D (e a)‖ ^ 2 - ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2) := by
    intro J
    set ε : J → H := fun a => e a with hε
    have hεon : Orthonormal ℝ ε := e.orthonormal.comp _ Subtype.val_injective
    obtain ⟨v, hv⟩ := ps_core ε hεon D Y hDs hYs hYD T K (fun h hon s hs => hTbound J h hon s hs)
      (fun h hon => hK J h hon)
    set h : J → H := rotVec v ε with hh
    have hhon : Orthonormal ℝ h := orthonormal_rotVec v hεon
    have hHS : ∑ i, ‖D (h i)‖ ^ 2 = ∑ a ∈ J, ‖D (e a)‖ ^ 2 := by
      rw [sum_norm_sq_swap e hDs h]
      have h1 : ∀ n, ∑ i, inner ℝ (h i) (D (e n)) ^ 2 = ∑ a : J, inner ℝ (D (ε a)) (e n) ^ 2 := fun n => by
        rw [hh, sum_sq_inner_rotVec v ε (D (e n))]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hDs, real_inner_comm]
      simp_rw [h1]
      have h2 : ∀ a : J, HasSum (fun n => inner ℝ (D (ε a)) (e n) ^ 2) (‖D (ε a)‖ ^ 2) := fun a =>
        hasSum_inner_sq e (D (ε a))
      rw [Summable.tsum_finsetSum (fun a _ => (h2 a).summable)]
      rw [← Finset.sum_coe_sort J (fun a => ‖D (e a)‖ ^ 2)]
      exact Finset.sum_congr rfl fun a _ => (h2 a).tsum_eq
    have hm : ∑ i, ∑ b : J, inner ℝ (D (h i)) (ε b) ^ 2 =
        ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2 := by
      rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      have : ∀ i, inner ℝ (D (h i)) (ε b) = inner ℝ (h i) (D (ε b)) := fun i => hDs _ _
      simp_rw [this]
      rw [hh, sum_sq_inner_rotVec v ε (D (ε b))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hDs]
    have hτ : ∑ i, ‖D (h i) - ∑ b, inner ℝ (D (h i)) (ε b) • ε b‖ ^ 2 =
        ∑ a ∈ J, ‖D (e a)‖ ^ 2 - ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2 := by
      simp_rw [norm_sub_sum_sq hεon, Finset.sum_sub_distrib]
      rw [hHS, hm]
    rw [hτ] at hv
    have hτnn : 0 ≤ ∑ a ∈ J, ‖D (e a)‖ ^ 2 - ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2 := by
      rw [← hτ]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    refine ⟨by linarith, by linarith⟩
  -- passage to the limit along finite sets
  set x : ι × ι → ℝ := fun p => inner ℝ (D (e p.1)) (e p.2) ^ 2 with hx
  have hxrow : ∀ a, HasSum (fun b => x (a, b)) (‖D (e a)‖ ^ 2) := fun a => hasSum_inner_sq e (D (e a))
  have hxsum : Summable x := by
    refine (summable_prod_of_nonneg (fun p => sq_nonneg _)).2 ⟨fun a => (hxrow a).summable, ?_⟩
    exact hDsum.congr fun a => ((hxrow a).tsum_eq).symm
  have hxtot : ∑' p, x p = ∑' a, ‖D (e a)‖ ^ 2 := by
    rw [hxsum.tsum_prod' (fun a => (hxrow a).summable)]
    exact tsum_congr fun a => (hxrow a).tsum_eq
  have hprod : Tendsto (fun J : Finset ι => J ×ˢ J) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun s => ⟨s.image Prod.fst ∪ s.image Prod.snd, fun J hJ p hp => ?_⟩
    refine Finset.mem_product.2 ⟨hJ ?_, hJ ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)
  have hm_eq : ∀ J : Finset ι, ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2 = ∑ p ∈ J ×ˢ J, x p := by
    intro J
    rw [Finset.sum_product]
    simp only [hx]
    rw [← Finset.sum_coe_sort J]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort J]
  have hm_lim : Tendsto (fun J : Finset ι => ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2) atTop
      (𝓝 (∑' a, ‖D (e a)‖ ^ 2)) := by
    simp_rw [hm_eq]
    rw [← hxtot]
    exact hxsum.hasSum.comp hprod
  have hHS_lim : Tendsto (fun J : Finset ι => ∑ a ∈ J, ‖D (e a)‖ ^ 2) atTop
      (𝓝 (∑' a, ‖D (e a)‖ ^ 2)) := hDsum.hasSum
  have hτ_lim : Tendsto (fun J : Finset ι => ∑ a ∈ J, ‖D (e a)‖ ^ 2 -
      ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2) atTop (𝓝 0) := by
    simpa using hHS_lim.sub hm_lim
  have hbound_lim : Tendsto (fun J : Finset ι => T + Real.sqrt (∑ a ∈ J, ‖D (e a)‖ ^ 2 -
        ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2) * Real.sqrt K +
        (∑ a ∈ J, ‖D (e a)‖ ^ 2 - ∑ a : J, ∑ b : J, inner ℝ (D (e a)) (e b) ^ 2)) atTop (𝓝 T) := by
    have h1 := ((Real.continuous_sqrt.tendsto 0).comp hτ_lim).mul_const (Real.sqrt K)
    have h2 := (tendsto_const_nhds (x := T)).add h1 |>.add hτ_lim
    simpa using h2
  refine ⟨hDsum, hDsum.tsum_le_of_sum_le fun J0 => ?_⟩
  refine ge_of_tendsto hbound_lim ?_
  filter_upwards [Filter.eventually_ge_atTop J0] with J hJ
  calc ∑ a ∈ J0, ‖D (e a)‖ ^ 2 ≤ ∑ a ∈ J, ‖D (e a)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hJ fun a _ _ => sq_nonneg _
    _ ≤ _ := (hfin J).2

end PSMain

end PSLimit
end FragPS2

section FragQ1
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section Padding
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- Extension by zero of a vector along an injection. -/
def padVec (e : ι₁ → ι₂) (v : ι₁ → ℝ) : ι₂ → ℝ := Function.extend e v 0

lemma padVec_apply (e : ι₁ → ι₂) (he : Function.Injective e) (v : ι₁ → ℝ) (i : ι₁) :
    padVec e v (e i) = v i := he.extend_apply v 0 i

lemma padVec_of_notMem (e : ι₁ → ι₂) (v : ι₁ → ℝ) {k : ι₂} (hk : k ∉ Set.range e) :
    padVec e v k = 0 := by
  unfold padVec
  rw [Function.extend_apply' _ _ _ (by simpa using hk)]
  rfl

lemma sum_padVec {M : Type*} [AddCommMonoid M] (e : ι₁ → ι₂) (he : Function.Injective e)
    (g : ℝ → M) (hg : g 0 = 0) (v : ι₁ → ℝ) :
    ∑ k, g (padVec e v k) = ∑ i, g (v i) := by
  symm
  refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) (fun i => ?_)
  · rw [padVec_of_notMem e v hk, hg]
  · rw [padVec_apply e he]

lemma measurable_padVec {α : Type*} {mα : MeasurableSpace α} (e : ι₁ → ι₂) (he : Function.Injective e)
    {v : α → ι₁ → ℝ} (hv : Measurable v) : Measurable fun a => padVec e (v a) := by
  refine measurable_pi_iff.2 fun k => ?_
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp_rw [padVec_apply e he]
    exact (measurable_pi_apply i).comp hv
  · simp_rw [padVec_of_notMem e _ hk]
    exact measurable_const

variable {ℱ : Filtration ℝ mΩ}

/-- Padding of a simple integrand along an injection of index sets. -/
def SimpleIntegrand.pad (e : ι₁ → ι₂) (he : Function.Injective e) (Ψ : SimpleIntegrand ℱ ι₁) :
    SimpleIntegrand ℱ ι₂ where
  n := Ψ.n
  t := Ψ.t
  mono := Ψ.mono
  nonneg := Ψ.nonneg
  ξ := fun i ω => padVec e (Ψ.ξ i ω)
  meas := fun i => measurable_padVec (mα := ℱ (Ψ.t i.castSucc)) e he (Ψ.meas i)
  bdd := by
    obtain ⟨C, hC⟩ := Ψ.bdd
    refine ⟨max C 0, fun i ω k => ?_⟩
    by_cases hk : k ∈ Set.range e
    · obtain ⟨j, rfl⟩ := hk
      show |padVec e (Ψ.ξ i ω) (e j)| ≤ max C 0
      rw [padVec_apply e he]
      exact (hC i ω j).trans (le_max_left _ _)
    · show |padVec e (Ψ.ξ i ω) k| ≤ max C 0
      rw [padVec_of_notMem e _ hk]
      simp

lemma SimpleIntegrand.pad_toFun (e : ι₁ → ι₂) (he : Function.Injective e) (Ψ : SimpleIntegrand ℱ ι₁)
    (s : ℝ) (ω : Ω) : (Ψ.pad e he).toFun s ω = padVec e (Ψ.toFun s ω) := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hk
    rw [padVec_apply e he, SimpleIntegrand.toFun_apply, SimpleIntegrand.toFun_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SimpleIntegrand.pad, padVec_apply e he]
  · rw [padVec_of_notMem e _ hk, SimpleIntegrand.toFun_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [SimpleIntegrand.pad, padVec_of_notMem e _ hk]
    simp

lemma SimpleIntegrand.pad_elemIntegral (e : ι₁ → ι₂) (he : Function.Injective e)
    (Ψ : SimpleIntegrand ℱ ι₁) (W : ℝ≥0 → Ω → ι₂ → ℝ) (s : ℝ) (ω : Ω) :
    (Ψ.pad e he).elemIntegral W s ω = Ψ.elemIntegral (fun t ω i => W t ω (e i)) s ω := by
  unfold SimpleIntegrand.elemIntegral
  refine Finset.sum_congr rfl fun i _ => ?_
  symm
  refine Fintype.sum_of_injective e he _ _ (fun k hk => ?_) (fun j => ?_)
  · simp only [SimpleIntegrand.pad, padVec_of_notMem e _ hk, zero_mul]
  · simp only [SimpleIntegrand.pad, padVec_apply e he]

/-- Extension by zero of an integrand along an injection of index sets. -/
def padFun (e : ι₁ → ι₂) (Φ : ℝ → Ω → ι₁ → ℝ) : ℝ → Ω → ι₂ → ℝ :=
  fun r ω => padVec e (Φ r ω)

variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma isProgressive_padFun (e : ι₁ → ι₂) (he : Function.Injective e) {Φ : ℝ → Ω → ι₁ → ℝ}
    (hΦ : IsProgressive ℱ Φ) : IsProgressive ℱ (padFun e Φ) := fun i =>
  measurable_padVec e he (hΦ i)

lemma sqIntegralOn_padFun (e : ι₁ → ι₂) (he : Function.Injective e) (Φ : ℝ → Ω → ι₁ → ℝ)
    (T : ℝ) : sqIntegralOn P (padFun e Φ) T = sqIntegralOn P Φ T := by
  unfold sqIntegralOn
  refine lintegral_congr fun ω => lintegral_congr fun s => ?_
  exact sum_padVec e he (fun x => ‖x‖ₑ ^ 2) (by simp) (Φ s ω)

lemma isProgressiveL2_padFun (e : ι₁ → ι₂) (he : Function.Injective e) {Φ : ℝ → Ω → ι₁ → ℝ}
    (hΦ : IsProgressiveL2 P ℱ Φ) : IsProgressiveL2 P ℱ (padFun e Φ) :=
  ⟨isProgressive_padFun e he hΦ.prog, fun T => by
    rw [sqIntegralOn_padFun e he]; exact hΦ.sq T⟩

lemma padVec_sub (e : ι₁ → ι₂) (he : Function.Injective e) (a b : ι₁ → ℝ) :
    padVec e a - padVec e b = padVec e (a - b) := by
  funext k
  by_cases hk : k ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hk
    simp [padVec_apply e he]
  · simp [padVec_of_notMem e _ hk]

theorem itoIntegral_pad (e : ι₁ → ι₂) (he : Function.Injective e) {W₂ : ℝ≥0 → Ω → ι₂ → ℝ}
    (hW₂ : IsBrownianFiltration P ℱ W₂)
    (hW₁ : IsBrownianFiltration P ℱ (fun t ω i => W₂ t ω (e i))) {Φ : ℝ → Ω → ι₁ → ℝ}
    (hΦ : IsProgressiveL2 P ℱ Φ) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ (fun t ω i => W₂ t ω (e i)) Φ t ω =
      itoIntegral P ℱ W₂ (padFun e Φ) t ω := by
  have hΦ₂ := isProgressiveL2_padFun e he hΦ
  have hM₂ := isItoIntegral_itoIntegral hW₂ hΦ₂
  have hM₁ : IsItoIntegral P ℱ (fun t ω i => W₂ t ω (e i)) Φ (itoIntegral P ℱ W₂ (padFun e Φ)) := by
    refine isItoIntegral_of_exists_seq hW₁ hΦ (continuous_itoIntegral P ℱ W₂ _)
      (adapted_itoIntegral P ℱ W₂ _) (fun t ht ω => itoIntegral_of_nonpos P ℱ W₂ _ ht ω) ?_
    intro t ht
    obtain ⟨Ψ, hΨ⟩ := exists_fast_approx hΦ
    have happ := isApprox_of_fast Ψ hΨ t
    refine ⟨Ψ, happ, ?_⟩
    have happ2 : IsApprox P (padFun e Φ) (fun n => (Ψ n).pad e he) t := by
      unfold IsApprox
      refine (happ).congr fun n => ?_
      have : (fun s ω => ((Ψ n).pad e he).toFun s ω - padFun e Φ s ω) =
          padFun e (fun s ω => (Ψ n).toFun s ω - Φ s ω) := by
        funext s ω
        simp only [padFun, SimpleIntegrand.pad_toFun]
        exact padVec_sub e he _ _
      rw [this, sqIntegralOn_padFun e he]
    have := hM₂.approx t ht (fun n => (Ψ n).pad e he) happ2
    simpa only [SimpleIntegrand.pad_elemIntegral] using this
  exact (isItoIntegral_itoIntegral hW₁ hΦ).ae_eq_forall hW₁ hM₁ hΦ |>.mono fun ω h t => h t |>.symm.symm

end Padding
end FragQ1

section FragQ2
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblDef
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
variable {A : Type*}

/-- The family `𝔚` restricted to a finite set of indices. -/
def WF (𝔚 : ℝ≥0 → Ω → A → ℝ) (F : Finset A) : ℝ≥0 → Ω → F → ℝ := fun t ω a => 𝔚 t ω a

/-- The integrand `ξ` restricted to a finite set of indices. -/
def ξF (ξ : ℝ → Ω → A → ℝ) (F : Finset A) : ℝ → Ω → F → ℝ := fun r ω a => ξ r ω a

/-- The `L²([0,T] × Ω)` size of the `a`-th coordinate. -/
def cT (P : Measure Ω) (ξ : ℝ → Ω → A → ℝ) (a : A) (T : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ‖ξ s ω a‖ₑ ^ 2) ∂P

/-- Integrands for the countable-index Itô integral: coordinatewise progressive, with
`∑_a E ∫_0^T |ξ_a|² < ∞` for every `T`. -/
structure IsCtbl (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (ξ : ℝ → Ω → A → ℝ) : Prop where
  prog : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)
  sq : ∀ T : ℝ, ∑' a, cT P ξ a T ≠ ⊤

variable {ξ : ℝ → Ω → A → ℝ}

lemma isProgressive_ξF (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (F : Finset A) :
    IsProgressive ℱ (ξF ξ F) :=
  isProgressive_pi (u := fun (a : F) r ω => ξ r ω a) fun a => hξ a

lemma measurable_cT_integrand (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (a : A) (T : ℝ) :
    Measurable (fun p : ℝ × Ω => ‖ξ (min p.1 T) p.2 a‖ₑ ^ 2) :=
  (measurable_clamp (hξ a) T).enorm.pow_const 2

lemma sqIntegralOn_ξF_eq_sum (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (F : Finset A)
    (T : ℝ) : sqIntegralOn P (ξF ξ F) T = ∑ a ∈ F, cT P ξ a T := by
  unfold sqIntegralOn cT
  have h1 : ∀ ω, ∫⁻ s in Set.Icc 0 T, ∑ a : F, ‖ξF ξ F s ω a‖ₑ ^ 2 =
      ∫⁻ s in Set.Icc 0 T, ∑ a ∈ F, ‖ξ (min s T) ω a‖ₑ ^ 2 := fun ω => by
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    rw [← Finset.sum_coe_sort F, min_eq_left hs.2]; rfl
  simp_rw [h1]
  have h2 : ∀ ω, ∫⁻ s in Set.Icc 0 T, ∑ a ∈ F, ‖ξ (min s T) ω a‖ₑ ^ 2 =
      ∑ a ∈ F, ∫⁻ s in Set.Icc 0 T, ‖ξ (min s T) ω a‖ₑ ^ 2 := fun ω =>
    lintegral_finset_sum _ fun a _ =>
      ((measurable_cT_integrand hξ a T).comp measurable_prodMk_right)
  simp_rw [h2]
  rw [lintegral_finset_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    refine lintegral_congr fun ω => ?_
    exact setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [min_eq_left hs.2]
  · intro a _
    exact ((measurable_cT_integrand hξ a T).comp
      (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 T))

lemma IsCtbl.progressiveL2 (hξ : IsCtbl P ℱ ξ) (F : Finset A) : IsProgressiveL2 P ℱ (ξF ξ F) := by
  refine ⟨isProgressive_ξF hξ.prog F, fun T => ?_⟩
  rw [sqIntegralOn_ξF_eq_sum hξ.prog]
  exact lt_of_le_of_lt (ENNReal.sum_le_tsum F) (lt_top_iff_ne_top.2 (hξ.sq T))

end CtblDef

section CtblKL
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ : ℝ → Ω → A → ℝ}

/-- The Itô integral of the restriction of `ξ` to the finite set `F`. -/
def ItoF (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (𝔚 : ℝ≥0 → Ω → A → ℝ) (ξ : ℝ → Ω → A → ℝ)
    (F : Finset A) : ℝ → Ω → ℝ :=
  itoIntegral P ℱ (WF 𝔚 F) (ξF ξ F)

/-- The inclusion of index sets. -/
def finIncl {F F' : Finset A} (h : F ⊆ F') : F → F' := fun a => ⟨a, h a.2⟩

lemma finIncl_injective {F F' : Finset A} (h : F ⊆ F') : Function.Injective (finIncl h) :=
  fun a b hab => Subtype.ext (congrArg (fun x : F' => (x : A)) hab)

lemma padFun_ξF {F F' : Finset A} (h : F ⊆ F') (r : ℝ) (ω : Ω) (a : F') :
    padFun (finIncl h) (ξF ξ F) r ω a = if (a : A) ∈ F then ξ r ω a else 0 := by
  by_cases ha : (a : A) ∈ F
  · rw [if_pos ha]
    have : a = finIncl h ⟨a, ha⟩ := rfl
    rw [this, padFun, padVec_apply _ (finIncl_injective h)]
    rfl
  · rw [if_neg ha]
    refine padVec_of_notMem _ _ ?_
    rintro ⟨b, hb⟩
    exact ha (by simpa using congrArg Subtype.val hb ▸ b.2)

lemma ItoF_sub (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ) {F F' : Finset A}
    (h : F ⊆ F') :
    ∀ᵐ ω ∂P, ∀ t, ItoF P ℱ 𝔚 ξ F' t ω - ItoF P ℱ 𝔚 ξ F t ω =
      itoIntegral P ℱ (WF 𝔚 F') (fun r ω (a : F') => if (a : A) ∈ F then 0 else ξ r ω a) t ω := by
  have hpad := itoIntegral_pad (finIncl h) (finIncl_injective h) (hW F') (hW₁ := hW F)
    (hξ.progressiveL2 F)
  have hsub := itoIntegral_sub (hW F') (hξ.progressiveL2 F')
    (isProgressiveL2_padFun (finIncl h) (finIncl_injective h) (hξ.progressiveL2 F))
  filter_upwards [hpad, hsub] with ω h1 h2 t
  have e : (fun s ω (k : F') => ξF ξ F' s ω k - padFun (finIncl h) (ξF ξ F) s ω k) =
      (fun r ω (a : F') => if (a : A) ∈ F then 0 else ξ r ω a) := by
    funext s ω a
    rw [padFun_ξF h]
    by_cases ha : (a : A) ∈ F <;> simp [ha, ξF]
  rw [e] at h2
  have h3 := h2 t
  have h4 := h1 t
  calc ItoF P ℱ 𝔚 ξ F' t ω - ItoF P ℱ 𝔚 ξ F t ω
      = itoIntegral P ℱ (fun t ω (k : F') => 𝔚 t ω k) (ξF ξ F') t ω -
        itoIntegral P ℱ (fun t ω (k : F') => 𝔚 t ω k) (padFun (finIncl h) (ξF ξ F)) t ω := by
        rw [← h4]; rfl
    _ = _ := h3.symm

end CtblKL
end FragQ2

section FragQ3
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section FastLimit
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

theorem ae_fast_of_martingales (D : ℕ → ℝ → Ω → ℝ) (hDm : ∀ n, Martingale (D n) ℱ P)
    (hDL2 : ∀ n t, MemLp (D n t) 2 P) (hDc : ∀ n ω, Continuous fun t => D n t ω)
    (hb : ∀ n N : ℕ, N ≤ n → ∫⁻ ω, ‖D n (N : ℝ) ω‖ₑ ^ 2 ∂P ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) :
    ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
      |D n t ω| ≤ (2⁻¹ : ℝ) ^ n := by
  rw [ae_all_iff]
  intro N
  set ε : ℕ → ℝ≥0 := fun n => (2⁻¹ : ℝ≥0) ^ n with hε
  set B : ℕ → Set Ω := fun n => if N ≤ n then
    {ω | ∃ t ∈ Set.Icc (0 : ℝ) N, (ε n : ℝ) < |D n t ω|} else ∅ with hB
  have hBle : ∀ n, P (B n) ≤ ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    by_cases hNn : N ≤ n
    · simp only [hB, hNn, ↓reduceIte]
      have hk := kolmogorov_cont (hDm n) (hDL2 n) (hDc n) (N := (N : ℝ)) (by positivity) (ε n)
      have hsq := hb n N hNn
      have hcoe : ((ε n : ℝ≥0) : ℝ≥0∞) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
        simp [hε, ENNReal.inv_pow]
      rw [hcoe] at hk
      have h1 : ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 * P {ω | ∃ t ∈ Set.Icc (0 : ℝ) N, (ε n : ℝ) < |D n t ω|} ≤
          ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 * ((2 : ℝ≥0∞)⁻¹ ^ n) := by
        refine hk.trans (hsq.trans (le_of_eq ?_))
        rw [pow_mul]; ring
      have hne0 : ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 ≠ 0 := by simp
      have hneT : ((2 : ℝ≥0∞)⁻¹ ^ n) ^ 2 ≠ ⊤ := by simp
      exact (ENNReal.mul_le_mul_iff_right hne0 hneT).1 h1
    · simp [hB, hNn]
  have hsum : ∑' n, P (B n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hBle)
    rw [ENNReal.tsum_geometric_two]
    norm_num
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 hω
  refine ⟨max n0 N, fun n hn t ht => ?_⟩
  have h1 := hn0 n (le_trans (le_max_left _ _) hn)
  have hNn : N ≤ n := (le_max_right _ _).trans hn
  simp only [hB, hNn, ↓reduceIte, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at h1
  have := h1 t ht
  simpa [hε] using this


/-- A sequence of continuous adapted processes with a.s. fast increments converges, a.s. for all
times simultaneously, to a continuous adapted process (the filtration being complete). -/
theorem exists_continuous_adapted_limit (hℱ : IsCompleteFiltration P ℱ) (I : ℕ → ℝ → Ω → ℝ)
    (hc : ∀ n ω, Continuous fun t => I n t ω) (hz : ∀ n t, t ≤ 0 → ∀ ω, I n t ω = 0)
    (had : ∀ n t, Measurable[ℱ t] (I n t))
    (hfast : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
      |I (n + 1) t ω - I n t ω| ≤ (2⁻¹ : ℝ) ^ n) :
    ∃ M : ℝ → Ω → ℝ, (∀ ω, Continuous fun t => M t ω) ∧ (∀ t ≤ 0, ∀ ω, M t ω = 0) ∧
      (∀ t, Measurable[ℱ t] (M t)) ∧
      ∀ᵐ ω ∂P, ∀ t, Tendsto (fun n => I n t ω) atTop (𝓝 (M t ω)) := by
  classical
  obtain ⟨C, hCm, hC0, hCG⟩ : ∃ C : Set Ω, MeasurableSet C ∧ P Cᶜ = 0 ∧ ∀ ω ∈ C, ∀ N : ℕ,
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
        |I (n + 1) t ω - I n t ω| ≤ (2⁻¹ : ℝ) ^ n := by
    refine ⟨(toMeasurable P {ω | ¬ (∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ t ∈ Set.Icc (0 : ℝ) N,
        |I (n + 1) t ω - I n t ω| ≤ (2⁻¹ : ℝ) ^ n)})ᶜ,
      (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hfast
    · intro ω hω
      by_contra hcon
      exact hω (subset_toMeasurable _ _ hcon)
  have hLim : ∀ ω ∈ C, ∃ L : ℝ → ℝ, Continuous L ∧
      ∀ t, Tendsto (fun n => I n t ω) atTop (𝓝 (L t)) := fun ω hω =>
    exists_continuous_limit (fun n t => I n t ω) (fun n => hc n ω) (fun n t ht => hz n t ht ω)
      (hCG ω hω)
  let M : ℝ → Ω → ℝ := fun t ω => if ω ∈ C then limUnder atTop (fun n => I n t ω) else 0
  have hMlim : ∀ ω ∈ C, ∀ t, Tendsto (fun n => I n t ω) atTop (𝓝 (M t ω)) := by
    intro ω hω t
    obtain ⟨L, _, hL⟩ := hLim ω hω
    have : M t ω = L t := by simp only [M, hω, ↓reduceIte]; exact (hL t).limUnder_eq
    rw [this]; exact hL t
  have hMcont : ∀ ω, Continuous fun t => M t ω := by
    intro ω
    by_cases hω : ω ∈ C
    · obtain ⟨L, hLc, hL⟩ := hLim ω hω
      have : (fun t => M t ω) = L := by
        funext t; simp only [M, hω, ↓reduceIte]; exact (hL t).limUnder_eq
      rw [this]; exact hLc
    · have : (fun t => M t ω) = fun _ => 0 := by funext t; simp [M, hω]
      rw [this]; exact continuous_const
  have hMzero : ∀ t ≤ 0, ∀ ω, M t ω = 0 := by
    intro t ht ω
    by_cases hω : ω ∈ C
    · have := hMlim ω hω t
      simp only [hz _ t ht ω] at this
      exact tendsto_nhds_unique tendsto_const_nhds this |>.symm
    · simp [M, hω]
  have hMad : ∀ t, Measurable[ℱ t] (M t) := by
    intro t
    have hCt : MeasurableSet[ℱ t] C := by
      have := hℱ t Cᶜ hCm.compl hC0
      simpa using this.compl
    have hf : ∀ n, Measurable[ℱ t] (C.indicator (I n t)) := fun n => (had n t).indicator hCt
    refine @measurable_of_tendsto_metrizable Ω ℝ (ℱ t) _ _ _ _ _ _ hf ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ C
    · simpa [Set.indicator_of_mem hω] using hMlim ω hω t
    · simp [M, hω]
  refine ⟨M, hMcont, hMzero, hMad, ?_⟩
  filter_upwards [(ae_iff.2 hC0 : ∀ᵐ ω ∂P, ω ∈ C)] with ω hω t using hMlim ω hω t

end FastLimit
end FragQ3

section FragQ4
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblTail
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ : ℝ → Ω → A → ℝ}

/-- The tail `∑_{a ∉ F} E ∫_0^T |ξ_a|²`. -/
def tailC (P : Measure Ω) (ξ : ℝ → Ω → A → ℝ) (F : Finset A) (T : ℝ) : ℝ≥0∞ :=
  ∑' b, if b ∈ F then 0 else cT P ξ b T

lemma cT_mono (P : Measure Ω) (ξ : ℝ → Ω → A → ℝ) (a : A) {T T' : ℝ} (h : T ≤ T') :
    cT P ξ a T ≤ cT P ξ a T' :=
  lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right h)

lemma tailC_mono_T (F : Finset A) {T T' : ℝ} (h : T ≤ T') : tailC P ξ F T ≤ tailC P ξ F T' :=
  ENNReal.tsum_le_tsum fun b => by
    by_cases hb : b ∈ F <;> simp [hb, cT_mono P ξ b h]

lemma tailC_anti (T : ℝ) {F F' : Finset A} (h : F ⊆ F') : tailC P ξ F' T ≤ tailC P ξ F T :=
  ENNReal.tsum_le_tsum fun b => by
    by_cases hb : b ∈ F
    · simp [hb, h hb]
    · by_cases hb' : b ∈ F' <;> simp [hb, hb']

lemma tailC_tendsto (hξ : IsCtbl P ℱ ξ) (T : ℝ) :
    Tendsto (fun F : Finset A => tailC P ξ F T) atTop (𝓝 0) := by
  have h := ENNReal.tendsto_tsum_compl_atTop_zero (hξ.sq T)
  refine h.congr fun F => ?_
  unfold tailC
  refine (tsum_subtype {x : A | x ∉ F} (fun b => cT P ξ b T)).trans ?_
  refine tsum_congr fun b => ?_
  by_cases hb : b ∈ F <;> simp [hb, Set.indicator]

lemma sum_diff_le_tailC (T : ℝ) {F F' : Finset A} :
    ∑ a ∈ F' \ F, cT P ξ a T ≤ tailC P ξ F T := by
  calc ∑ a ∈ F' \ F, cT P ξ a T = ∑ a ∈ F', (if a ∈ F then 0 else cT P ξ a T) := by
        rw [Finset.sdiff_eq_filter, Finset.sum_filter]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases ha : a ∈ F <;> simp [ha]
    _ ≤ tailC P ξ F T := ENNReal.sum_le_tsum F'

lemma tailC_le_tsum (F : Finset A) (T : ℝ) : tailC P ξ F T ≤ ∑' b, cT P ξ b T :=
  ENNReal.tsum_le_tsum fun b => by by_cases hb : b ∈ F <;> simp [hb]

/-- The integrand `1_{a ∉ F} ξ_a` as an integrand on `A`. -/
def ξtail (ξ : ℝ → Ω → A → ℝ) (F : Finset A) : ℝ → Ω → A → ℝ :=
  fun r ω a => if a ∈ F then 0 else ξ r ω a

lemma cT_ξtail (F : Finset A) (a : A) (T : ℝ) :
    cT P (ξtail ξ F) a T = if a ∈ F then 0 else cT P ξ a T := by
  by_cases ha : a ∈ F <;> simp [cT, ξtail, ha]

lemma isProgressive_ξtail (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (F : Finset A) :
    ∀ a, IsProgressive ℱ (fun r ω => ξtail ξ F r ω a) := fun a => by
  by_cases ha : a ∈ F
  · simp only [ξtail, ha, if_true]; exact isProgressive_const ℱ (0 : ℝ)
  · simp only [ξtail, ha, if_false]; exact hξ a

lemma sqIntegralOn_tail_le (hξ : IsCtbl P ℱ ξ) (F F' : Finset A) (T : ℝ) :
    sqIntegralOn P (ξF (ξtail ξ F) F') T ≤ tailC P ξ F T := by
  rw [sqIntegralOn_ξF_eq_sum (isProgressive_ξtail hξ.prog F)]
  simp_rw [cT_ξtail]
  exact ENNReal.sum_le_tsum F'

lemma isProgressiveL2_tail (hξ : IsCtbl P ℱ ξ) (F F' : Finset A) :
    IsProgressiveL2 P ℱ (ξF (ξtail ξ F) F') := by
  refine ⟨isProgressive_ξF (isProgressive_ξtail hξ.prog F) F', fun T => ?_⟩
  exact lt_of_le_of_lt (sqIntegralOn_tail_le hξ F F' T)
    (lt_of_le_of_lt (tailC_le_tsum F T) (lt_top_iff_ne_top.2 (hξ.sq T)))

lemma exists_fast_finsets (hξ : IsCtbl P ℱ ξ) :
    ∃ G : ℕ → Finset A, Monotone G ∧ ∀ n : ℕ, tailC P ξ (G n) n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
  have : ∀ n : ℕ, ∃ F : Finset A, tailC P ξ F n ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
    intro n
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := ENNReal.pow_pos (by simp) _
    obtain ⟨F, hF⟩ := ((tailC_tendsto hξ (n : ℝ)).eventually (gt_mem_nhds hpos)).exists
    exact ⟨F, hF.le⟩
  choose F hF using this
  refine ⟨fun n => (Finset.range (n + 1)).biUnion F, ?_, fun n => ?_⟩
  · intro m n hmn
    exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_subset_range.2 (by omega))
  · refine (tailC_anti (n : ℝ) ?_).trans (hF n)
    exact Finset.subset_biUnion_of_mem F (Finset.mem_range.2 (Nat.lt_succ_self n))

end CtblTail
end FragQ4

section FragQ5
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblExist
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ : ℝ → Ω → A → ℝ}

/-- `I` is the Itô integral `∫_0^· ∑_a ξ_a d𝔚^a` of a countable family: a continuous adapted process
vanishing on `(-∞, 0]` which is the `L²` limit of the Itô integrals over finite sets of indices. -/
structure IsItoC (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (𝔚 : ℝ≥0 → Ω → A → ℝ)
    (ξ : ℝ → Ω → A → ℝ) (I : ℝ → Ω → ℝ) : Prop where
  cont : ∀ ω, Continuous fun t => I t ω
  adapted : ∀ t, Measurable[ℱ t] (I t)
  zero : ∀ t ≤ 0, ∀ ω, I t ω = 0
  approx : ∀ t : ℝ, 0 ≤ t → Tendsto (fun F : Finset A =>
    ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)

theorem exists_isItoC (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ) :
    ∃ I, IsItoC P ℱ 𝔚 ξ I := by
  obtain ⟨G, hGmono, hG⟩ := exists_fast_finsets hξ
  have hℱ : IsCompleteFiltration P ℱ := (hW ∅).complete
  set I : ℕ → ℝ → Ω → ℝ := fun n => ItoF P ℱ 𝔚 ξ (G n) with hI
  have hIc : ∀ n ω, Continuous fun t => I n t ω := fun n ω =>
    continuous_itoIntegral P ℱ _ _ ω
  have hIz : ∀ n t, t ≤ 0 → ∀ ω, I n t ω = 0 := fun n t ht ω =>
    itoIntegral_of_nonpos P ℱ _ _ ht ω
  have hIad : ∀ n t, Measurable[ℱ t] (I n t) := fun n t => adapted_itoIntegral P ℱ _ _ t
  have hIm : ∀ n, Martingale (I n) ℱ P := fun n =>
    martingale_itoIntegral (hW (G n)) (hξ.progressiveL2 (G n))
  have hIL2 : ∀ n t, MemLp (I n t) 2 P := fun n t =>
    memLp_two_itoIntegral (hW (G n)) (hξ.progressiveL2 (G n)) t
  -- increments
  have hDm : ∀ n, Martingale (fun t ω => I (n + 1) t ω - I n t ω) ℱ P := fun n =>
    (hIm (n + 1)).sub (hIm n)
  have hDL2 : ∀ n t, MemLp (fun ω => I (n + 1) t ω - I n t ω) 2 P := fun n t =>
    (hIL2 (n + 1) t).sub (hIL2 n t)
  have hDc : ∀ n ω, Continuous fun t => I (n + 1) t ω - I n t ω := fun n ω =>
    (hIc (n + 1) ω).sub (hIc n ω)
  have hsub : ∀ n, ∀ᵐ ω ∂P, ∀ t, I (n + 1) t ω - I n t ω =
      itoIntegral P ℱ (WF 𝔚 (G (n + 1))) (ξF (ξtail ξ (G n)) (G (n + 1))) t ω := fun n =>
    ItoF_sub hW hξ (hGmono (Nat.le_succ n))
  have hbL2 : ∀ n (t : ℝ), ∫⁻ ω, ‖I (n + 1) t ω - I n t ω‖ₑ ^ 2 ∂P ≤ tailC P ξ (G n) t := by
    intro n t
    calc ∫⁻ ω, ‖I (n + 1) t ω - I n t ω‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ‖itoIntegral P ℱ (WF 𝔚 (G (n + 1))) (ξF (ξtail ξ (G n)) (G (n + 1))) t ω‖ₑ ^ 2 ∂P :=
          lintegral_congr_ae (by filter_upwards [hsub n] with ω hω; rw [hω t])
      _ = sqIntegralOn P (ξF (ξtail ξ (G n)) (G (n + 1))) t :=
          lintegral_itoIntegral_sq (hW (G (n + 1))) (isProgressiveL2_tail hξ (G n) (G (n + 1))) t
      _ ≤ _ := sqIntegralOn_tail_le hξ (G n) (G (n + 1)) t
  have hb : ∀ n N : ℕ, N ≤ n → ∫⁻ ω, ‖I (n + 1) (N : ℝ) ω - I n (N : ℝ) ω‖ₑ ^ 2 ∂P ≤
      ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := fun n N hNn =>
    (hbL2 n N).trans ((tailC_mono_T (G n) (by exact_mod_cast hNn)).trans (hG n))
  have hfast := ae_fast_of_martingales (fun n t ω => I (n + 1) t ω - I n t ω) hDm hDL2 hDc hb
  obtain ⟨M, hMc, hMz, hMad, hMlim⟩ :=
    exists_continuous_adapted_limit hℱ I hIc hIz hIad hfast
  refine ⟨M, ⟨hMc, hMad, hMz, fun t ht => ?_⟩⟩
  -- `L²` convergence along the chain `G n`
  have hmeasI : ∀ n s, AEMeasurable (I n s) P := fun n s =>
    ((hIad n s).mono (ℱ.le s) le_rfl).aemeasurable
  have h1 : ∀ n, ∫⁻ ω, ‖I n t ω - M t ω‖ₑ ^ 2 ∂P ≤ tailC P ξ (G n) t := by
    intro n
    have := lintegral_enorm_sq_le_liminf (P := P) (X := fun m => I m t) (Y := M t) (Z := I n t)
      (fun m => hmeasI m t) (hmeasI n t) (hMlim.mono fun ω hω => hω t)
    refine this.trans ?_
    refine liminf_le_of_frequently_le' ?_
    refine Filter.Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    have hsubm : ∀ᵐ ω ∂P, ∀ s, ItoF P ℱ 𝔚 ξ (G m) s ω - ItoF P ℱ 𝔚 ξ (G n) s ω =
        itoIntegral P ℱ (WF 𝔚 (G m)) (ξF (ξtail ξ (G n)) (G m)) s ω :=
      ItoF_sub hW hξ (hGmono hm)
    calc ∫⁻ ω, ‖I n t ω - I m t ω‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ‖itoIntegral P ℱ (WF 𝔚 (G m)) (ξF (ξtail ξ (G n)) (G m)) t ω‖ₑ ^ 2 ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hsubm] with ω hω
          rw [← hω t, ← enorm_neg, neg_sub]
      _ = sqIntegralOn P (ξF (ξtail ξ (G n)) (G m)) t :=
          lintegral_itoIntegral_sq (hW (G m)) (isProgressiveL2_tail hξ (G n) (G m)) t
      _ ≤ _ := sqIntegralOn_tail_le hξ (G n) (G m) t
  have hu : Tendsto (fun n : ℕ => 4 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (3 * n)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((2 : ℝ≥0∞)⁻¹) ^ 3) (by
        rw [← ENNReal.inv_pow]; norm_num)
      simpa [pow_mul] using this
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤))
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨n, hn1, hn2⟩ :=
    ((hu.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop ⌈t⌉₊)).exists
  filter_upwards [eventually_ge_atTop (G n)] with F hF
  have hsubF : ∀ᵐ ω ∂P, ∀ s, ItoF P ℱ 𝔚 ξ F s ω - ItoF P ℱ 𝔚 ξ (G n) s ω =
      itoIntegral P ℱ (WF 𝔚 F) (ξF (ξtail ξ (G n)) F) s ω := ItoF_sub hW hξ hF
  have htn : t ≤ (n : ℝ) := (Nat.le_ceil t).trans (by exact_mod_cast hn2)
  have htail : tailC P ξ (G n) t ≤ ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) :=
    (tailC_mono_T (G n) htn).trans (hG n)
  have h2 : ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I n t ω‖ₑ ^ 2 ∂P ≤ tailC P ξ (G n) t := by
    calc ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I n t ω‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ‖itoIntegral P ℱ (WF 𝔚 F) (ξF (ξtail ξ (G n)) F) t ω‖ₑ ^ 2 ∂P :=
          lintegral_congr_ae (by filter_upwards [hsubF] with ω hω; rw [← hω t])
      _ = sqIntegralOn P (ξF (ξtail ξ (G n)) F) t :=
          lintegral_itoIntegral_sq (hW F) (isProgressiveL2_tail hξ (G n) F) t
      _ ≤ _ := sqIntegralOn_tail_le hξ (G n) F t
  have hmF : Measurable fun ω => ‖ItoF P ℱ 𝔚 ξ F t ω - I n t ω‖ₑ ^ 2 :=
    ((((adapted_itoIntegral P ℱ _ _ t).mono (ℱ.le t) le_rfl).sub
      ((hIad n t).mono (ℱ.le t) le_rfl)).enorm).pow_const 2
  calc ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - M t ω‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (2 * ‖ItoF P ℱ 𝔚 ξ F t ω - I n t ω‖ₑ ^ 2 + 2 * ‖I n t ω - M t ω‖ₑ ^ 2) ∂P := by
        refine lintegral_mono fun ω => ?_
        have := enorm_add_sq_le (ItoF P ℱ 𝔚 ξ F t ω - I n t ω) (I n t ω - M t ω)
        simpa using this
    _ = 2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I n t ω‖ₑ ^ 2 ∂P +
          2 * ∫⁻ ω, ‖I n t ω - M t ω‖ₑ ^ 2 ∂P := by
        rw [lintegral_add_left (hmF.const_mul 2), lintegral_const_mul _ hmF,
          lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) + 2 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
        gcongr
        · exact h2.trans htail
        · exact (h1 n).trans htail
    _ = 4 * ((2 : ℝ≥0∞)⁻¹) ^ (3 * n) := by
        rw [← add_mul]; norm_num
    _ ≤ ε := hn1.le

end CtblExist
end FragQ5

section FragQ6
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblProps
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ ξ' : ℝ → Ω → A → ℝ}
  {I I' : ℝ → Ω → ℝ}

lemma aemeasurable_ItoF (F : Finset A) (t : ℝ) : AEMeasurable (ItoF P ℱ 𝔚 ξ F t) P :=
  ((adapted_itoIntegral P ℱ _ _ t).mono (ℱ.le t) le_rfl).aemeasurable

lemma IsItoC.aemeasurable (hI : IsItoC P ℱ 𝔚 ξ I) (t : ℝ) : AEMeasurable (I t) P :=
  ((hI.adapted t).mono (ℱ.le t) le_rfl).aemeasurable

lemma lintegral_enorm_sq_add_le' {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P) :
    ∫⁻ ω, ‖X ω + Y ω‖ₑ ^ 2 ∂P ≤ 2 * ∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂P := by
  calc ∫⁻ ω, ‖X ω + Y ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, (2 * ‖X ω‖ₑ ^ 2 + 2 * ‖Y ω‖ₑ ^ 2) ∂P :=
        lintegral_mono fun ω => enorm_add_sq_le _ _
    _ = _ := by
        rw [lintegral_add_left' (hX.enorm.pow_const 2 |>.const_mul 2),
          lintegral_const_mul'' _ (hX.enorm.pow_const 2), lintegral_const_mul'' _ (hY.enorm.pow_const 2)]

/-- Uniqueness of the countable Itô integral. -/
theorem IsItoC.ae_eq_forall (hI : IsItoC P ℱ 𝔚 ξ I) (hI' : IsItoC P ℱ 𝔚 ξ I') :
    ∀ᵐ ω ∂P, ∀ t, I t ω = I' t ω := by
  refine ae_forall_eq_of_continuous P I I' hI.cont hI'.cont fun t => ?_
  rcases le_or_gt t 0 with ht | ht
  · exact Filter.Eventually.of_forall fun ω => by rw [hI.zero t ht ω, hI'.zero t ht ω]
  have h1 := hI.approx t ht.le
  have h2 := hI'.approx t ht.le
  have hm := (hI.aemeasurable t).sub (hI'.aemeasurable t)
  have h0 : ∫⁻ ω, ‖I t ω - I' t ω‖ₑ ^ 2 ∂P = 0 := by
    refine le_antisymm ?_ bot_le
    have h3 : Tendsto (fun F : Finset A => 2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 ∂P +
        2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I' t ω‖ₑ ^ 2 ∂P) atTop (𝓝 (2 * 0 + 2 * 0)) :=
      (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num))).add
        (ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num)))
    simp only [mul_zero, add_zero] at h3
    refine ge_of_tendsto' h3 fun F => ?_
    have hF := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) F t
    have := lintegral_enorm_sq_add_le' (P := P) (hF.sub (hI.aemeasurable t)) ((hI'.aemeasurable t).sub hF)
    have e : ∀ ω, (ItoF P ℱ 𝔚 ξ F t ω - I t ω) + (I' t ω - ItoF P ℱ 𝔚 ξ F t ω) = I' t ω - I t ω := fun ω => by ring
    simp only [Pi.sub_apply, e] at this
    calc ∫⁻ ω, ‖I t ω - I' t ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖I' t ω - I t ω‖ₑ ^ 2 ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← enorm_neg, neg_sub]
      _ ≤ _ := this
      _ = _ := by
          congr 2
          refine lintegral_congr fun ω => ?_
          rw [← enorm_neg, neg_sub]
  filter_upwards [ae_eq_zero_of_lintegral_enorm_sq_eq_zero hm h0] with ω hω
  simpa [sub_eq_zero] using hω

theorem IsItoC.add (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ')
    (hI : IsItoC P ℱ 𝔚 ξ I) (hI' : IsItoC P ℱ 𝔚 ξ' I') :
    IsItoC P ℱ 𝔚 (fun r ω a => ξ r ω a + ξ' r ω a) (fun t ω => I t ω + I' t ω) := by
  refine ⟨fun ω => (hI.cont ω).add (hI'.cont ω), fun t => (hI.adapted t).add (hI'.adapted t),
    fun t ht ω => by simp [hI.zero t ht ω, hI'.zero t ht ω], fun t ht => ?_⟩
  have h1 := hI.approx t ht
  have h2 := hI'.approx t ht
  have hb : Tendsto (fun F : Finset A => 2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 ∂P +
      2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ' F t ω - I' t ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
        (ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le) fun F => ?_
  have hae := itoIntegral_add (hW F) (hξ.progressiveL2 F) (hξ'.progressiveL2 F)
  have hF := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) F t
  have hF' := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ') F t
  calc ∫⁻ ω, ‖ItoF P ℱ 𝔚 (fun r ω a => ξ r ω a + ξ' r ω a) F t ω - (I t ω + I' t ω)‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ‖(ItoF P ℱ 𝔚 ξ F t ω - I t ω) + (ItoF P ℱ 𝔚 ξ' F t ω - I' t ω)‖ₑ ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω hω
        have : ItoF P ℱ 𝔚 (fun r ω a => ξ r ω a + ξ' r ω a) F t ω =
            ItoF P ℱ 𝔚 ξ F t ω + ItoF P ℱ 𝔚 ξ' F t ω := hω t
        rw [this]; congr 2; ring
    _ ≤ _ := lintegral_enorm_sq_add_le' (hF.sub (hI.aemeasurable t)) (hF'.sub (hI'.aemeasurable t))

theorem IsItoC.sub (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ')
    (hI : IsItoC P ℱ 𝔚 ξ I) (hI' : IsItoC P ℱ 𝔚 ξ' I') :
    IsItoC P ℱ 𝔚 (fun r ω a => ξ r ω a - ξ' r ω a) (fun t ω => I t ω - I' t ω) := by
  refine ⟨fun ω => (hI.cont ω).sub (hI'.cont ω), fun t => (hI.adapted t).sub (hI'.adapted t),
    fun t ht ω => by simp [hI.zero t ht ω, hI'.zero t ht ω], fun t ht => ?_⟩
  have h1 := hI.approx t ht
  have h2 := hI'.approx t ht
  have hb : Tendsto (fun F : Finset A => 2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 ∂P +
      2 * ∫⁻ ω, ‖-(ItoF P ℱ 𝔚 ξ' F t ω - I' t ω)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [enorm_neg]
    have := (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
        (ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le) fun F => ?_
  have hae := itoIntegral_sub (hW F) (hξ.progressiveL2 F) (hξ'.progressiveL2 F)
  have hF := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) F t
  have hF' := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ') F t
  calc ∫⁻ ω, ‖ItoF P ℱ 𝔚 (fun r ω a => ξ r ω a - ξ' r ω a) F t ω - (I t ω - I' t ω)‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ‖(ItoF P ℱ 𝔚 ξ F t ω - I t ω) + -(ItoF P ℱ 𝔚 ξ' F t ω - I' t ω)‖ₑ ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω hω
        have : ItoF P ℱ 𝔚 (fun r ω a => ξ r ω a - ξ' r ω a) F t ω =
            ItoF P ℱ 𝔚 ξ F t ω - ItoF P ℱ 𝔚 ξ' F t ω := hω t
        rw [this]; congr 2; ring
    _ ≤ _ := lintegral_enorm_sq_add_le' (hF.sub (hI.aemeasurable t)) ((hF'.sub (hI'.aemeasurable t)).neg)

theorem IsItoC.smul (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ) (c : ℝ)
    (hI : IsItoC P ℱ 𝔚 ξ I) :
    IsItoC P ℱ 𝔚 (fun r ω a => c * ξ r ω a) (fun t ω => c * I t ω) := by
  refine ⟨fun ω => (hI.cont ω).const_mul c, fun t => (hI.adapted t).const_mul c,
    fun t ht ω => by simp [hI.zero t ht ω], fun t ht => ?_⟩
  have h1 := hI.approx t ht
  have hb : Tendsto (fun F : Finset A => ‖c‖ₑ ^ 2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul h1 (Or.inr (by simp : ‖c‖ₑ ^ 2 ≠ ⊤))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le) fun F => ?_
  have hae := itoIntegral_smul (hW F) (hξ.progressiveL2 F) c
  have hF := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) F t
  calc ∫⁻ ω, ‖ItoF P ℱ 𝔚 (fun r ω a => c * ξ r ω a) F t ω - c * I t ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ‖c‖ₑ ^ 2 * ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with ω hω
        have : ItoF P ℱ 𝔚 (fun r ω a => c * ξ r ω a) F t ω = c * ItoF P ℱ 𝔚 ξ F t ω := hω t
        rw [this, ← mul_sub, enorm_mul, mul_pow]
    _ = _ := lintegral_const_mul'' _ ((hF.sub (hI.aemeasurable t)).enorm.pow_const 2)
    _ ≤ _ := le_rfl

/-- If `ξ` vanishes outside the finite set `F₀`, its countable integral is the finite one. -/
theorem isItoC_of_support (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ) (F₀ : Finset A)
    (h0 : ∀ r ω a, a ∉ F₀ → ξ r ω a = 0) : IsItoC P ℱ 𝔚 ξ (ItoF P ℱ 𝔚 ξ F₀) := by
  refine ⟨fun ω => continuous_itoIntegral P ℱ _ _ ω, fun t => adapted_itoIntegral P ℱ _ _ t,
    fun t ht ω => itoIntegral_of_nonpos P ℱ _ _ ht ω, fun t ht => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop F₀] with F hF
  have hsub := ItoF_sub hW hξ hF
  have hz : ξtail ξ F₀ = fun _ _ _ => 0 := by
    funext r ω a
    by_cases ha : a ∈ F₀ <;> simp [ξtail, ha, h0 r ω a]
  have hconst := itoIntegral_const (hW F) (fun _ : F => (0 : ℝ))
  symm
  have : ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F t ω - ItoF P ℱ 𝔚 ξ F₀ t ω‖ₑ ^ 2 ∂P = ∫⁻ ω, (0 : ℝ≥0∞) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hsub, hconst] with ω h1 h2
    rw [h1 t]
    have : (fun r ω (a : F) => if (a : A) ∈ F₀ then (0 : ℝ) else ξ r ω a) = fun _ _ _ => (0 : ℝ) := by
      funext r ω a; by_cases ha : (a : A) ∈ F₀ <;> simp [ha, h0 r ω a]
    rw [this]
    have h3 : itoIntegral P ℱ (WF 𝔚 F) (fun _ _ (_ : F) => (0 : ℝ)) t ω = 0 :=
      (h2 t).trans (by simp)
    rw [h3]
    simp
  rw [this]; simp

lemma exists_finset_seq : ∃ F : ℕ → Finset A, Tendsto F atTop atTop :=
  Filter.exists_seq_tendsto _

theorem IsItoC.memLp (hξ : IsCtbl P ℱ ξ) (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hI : IsItoC P ℱ 𝔚 ξ I) {t : ℝ} (ht : 0 ≤ t) : MemLp (I t) 2 P := by
  obtain ⟨F, hF⟩ := exists_finset_seq (A := A)
  exact memLp_of_tendsto_lintegral (X := fun n => ItoF P ℱ 𝔚 ξ (F n) t)
    (hI.aemeasurable t).aestronglyMeasurable
    (fun n => memLp_two_itoIntegral (hW (F n)) (hξ.progressiveL2 (F n)) t)
    ((hI.approx t ht).comp hF)

/-- The `L²`-isometry, upper bound: `E|I_t|² ≤ ∑_a E ∫_0^t |ξ_a|²`. -/
theorem IsItoC.lintegral_sq_le (hξ : IsCtbl P ℱ ξ) (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hI : IsItoC P ℱ 𝔚 ξ I) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ‖I t ω‖ₑ ^ 2 ∂P ≤ ∑' a, cT P ξ a t := by
  obtain ⟨F, hF⟩ := exists_finset_seq (A := A)
  have hY := hI.memLp hξ hW ht
  have hX : ∀ n, MemLp (ItoF P ℱ 𝔚 ξ (F n) t) 2 P := fun n =>
    memLp_two_itoIntegral (hW (F n)) (hξ.progressiveL2 (F n)) t
  have hlim := tendsto_toLp_of_tendsto_lintegral hX hY ((hI.approx t ht).comp hF)
  have hS : ∑' a, cT P ξ a t ≠ ⊤ := hξ.sq t
  have hbound : ∀ n, ‖(hX n).toLp (ItoF P ℱ 𝔚 ξ (F n) t)‖ ^ 2 ≤ (∑' a, cT P ξ a t).toReal := by
    intro n
    rw [norm_toLp_sq]
    refine ENNReal.toReal_mono hS ?_
    have e : ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ (F n) t ω‖ₑ ^ 2 ∂P = sqIntegralOn P (ξF ξ (F n)) t :=
      lintegral_itoIntegral_sq (hW (F n)) (hξ.progressiveL2 (F n)) t
    rw [e, sqIntegralOn_ξF_eq_sum hξ.prog]
    exact ENNReal.sum_le_tsum _
  have h2 : ‖hY.toLp (I t)‖ ^ 2 ≤ (∑' a, cT P ξ a t).toReal := by
    have := (hlim.norm).pow 2
    exact le_of_tendsto this (Filter.Eventually.of_forall hbound)
  rw [norm_toLp_sq] at h2
  have hfin : ∫⁻ ω, ‖I t ω‖ₑ ^ 2 ∂P ≠ ⊤ := (lintegral_enorm_sq_lt_top hY).ne
  exact (ENNReal.toReal_le_toReal hfin hS).1 h2

end CtblProps
end FragQ6

section FragQ7
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblMart
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ ξ' : ℝ → Ω → A → ℝ}
  {I I' : ℝ → Ω → ℝ}

/-- `L²` convergence gives convergence of `L²` norms (in `ℝ≥0∞`). -/
lemma tendsto_lintegral_sq_of_L2 {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} (hX : ∀ n, MemLp (X n) 2 P)
    (hY : MemLp Y 2 P) (h : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Y ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖X n ω‖ₑ ^ 2 ∂P) atTop (𝓝 (∫⁻ ω, ‖Y ω‖ₑ ^ 2 ∂P)) := by
  have hlim := tendsto_toLp_of_tendsto_lintegral hX hY h
  have h2 := (hlim.norm).pow 2
  simp_rw [norm_toLp_sq] at h2
  have := (ENNReal.tendsto_toReal_iff (fun n => (lintegral_enorm_sq_lt_top (hX n)).ne)
    (lintegral_enorm_sq_lt_top hY).ne).1 h2
  exact this

lemma tendsto_setIntegral_ItoF (hξ : IsCtbl P ℱ ξ) (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hI : IsItoC P ℱ 𝔚 ξ I) (u : ℝ) {S : Set Ω} (hS : MeasurableSet S) {F : ℕ → Finset A}
    (hF : Tendsto F atTop atTop) :
    Tendsto (fun n => ∫ ω in S, ItoF P ℱ 𝔚 ξ (F n) u ω ∂P) atTop (𝓝 (∫ ω in S, I u ω ∂P)) := by
  rcases lt_or_ge u 0 with hu | hu
  · have e1 : ∀ n, ItoF P ℱ 𝔚 ξ (F n) u = fun _ => 0 := fun n =>
      funext fun ω => itoIntegral_of_nonpos P ℱ _ _ hu.le ω
    have e2 : I u = fun _ => 0 := funext fun ω => hI.zero u hu.le ω
    simp [e1, e2]
  · exact tendsto_setIntegral_of_tendsto_lintegral
      (fun n => memLp_two_itoIntegral (hW (F n)) (hξ.progressiveL2 (F n)) u)
      (hI.memLp hξ hW hu) ((hI.approx u hu).comp hF) hS

theorem IsItoC.martingale (hξ : IsCtbl P ℱ ξ) (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hI : IsItoC P ℱ 𝔚 ξ I) : Martingale I ℱ P := by
  have hsa : StronglyAdapted ℱ I := fun t => (hI.adapted t).stronglyMeasurable
  have hMemLp : ∀ t, MemLp (I t) 2 P := fun t => by
    rcases lt_or_ge t 0 with ht | ht
    · have : I t = fun _ => 0 := funext fun ω => hI.zero t ht.le ω
      rw [this]; exact MemLp.zero'
    · exact hI.memLp hξ hW ht
  obtain ⟨F, hF⟩ := exists_finset_seq (A := A)
  refine ⟨hsa, fun i j hij => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) ((hMemLp j).integrable one_le_two)
    (fun s _ _ => ((hMemLp i).integrable one_le_two).integrableOn) (fun s hs _ => ?_)
    (hsa i).aestronglyMeasurable
  have hsm : MeasurableSet s := ℱ.le i s hs
  have h1 := tendsto_setIntegral_ItoF hξ hW hI i hsm hF
  have h2 := tendsto_setIntegral_ItoF hξ hW hI j hsm hF
  have h3 : ∀ n, ∫ ω in s, ItoF P ℱ 𝔚 ξ (F n) i ω ∂P = ∫ ω in s, ItoF P ℱ 𝔚 ξ (F n) j ω ∂P :=
    fun n => (martingale_itoIntegral (hW (F n)) (hξ.progressiveL2 (F n))).setIntegral_eq hij hs
  simp_rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

end CtblMart
end FragQ7

section FragQ8
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblCond
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ ξ' : ℝ → Ω → A → ℝ}
  {I I' : ℝ → Ω → ℝ}

/-- The `L²` size of the `a`-th coordinate on `S × (s, t]`. -/
def cS (P : Measure Ω) (ξ : ℝ → Ω → A → ℝ) (a : A) (S : Set Ω) (s t : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω in S, (∫⁻ r in Set.Ioc s t, ‖ξ r ω a‖ₑ ^ 2) ∂P

lemma sqIntegralOn_restrictFun_eq {ι : Type*} [Fintype ι] (Φ : ℝ → Ω → ι → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) {S : Set Ω} (hS : MeasurableSet S) :
    sqIntegralOn P (restrictFun Φ s t S) t =
      ∫⁻ ω in S, (∫⁻ r in Set.Ioc s t, ∑ k, ‖Φ r ω k‖ₑ ^ 2) ∂P := by
  unfold sqIntegralOn
  rw [← lintegral_indicator hS]
  refine lintegral_congr fun ω => ?_
  by_cases hω : ω ∈ S
  · rw [Set.indicator_of_mem hω]
    have : ∀ r, ∑ k, ‖restrictFun Φ s t S r ω k‖ₑ ^ 2 =
        (Set.Ioc s t).indicator (fun r => ∑ k, ‖Φ r ω k‖ₑ ^ 2) r := fun r => by
      by_cases hr : r ∈ Set.Ioc s t <;> simp [restrictFun, hω, hr]
    simp_rw [this]
    rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
    have hI : Set.Icc 0 t ∩ Set.Ioc s t = Set.Ioc s t := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨hs.trans h1.le, h2⟩, h1, h2⟩
    rw [Set.inter_comm, hI]
  · rw [Set.indicator_of_notMem hω]
    simp [restrictFun, hω]

lemma lintegral_finset_sum_Ioc (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (F : Finset A)
    {s t : ℝ} (hst : s ≤ t) (S : Set Ω) :
    ∫⁻ ω in S, (∫⁻ r in Set.Ioc s t, ∑ a ∈ F, ‖ξ r ω a‖ₑ ^ 2) ∂P =
      ∑ a ∈ F, cS P ξ a S s t := by
  have hcl : ∀ a ω, ∫⁻ r in Set.Ioc s t, ‖ξ r ω a‖ₑ ^ 2 =
      ∫⁻ r in Set.Ioc s t, ‖ξ (min r t) ω a‖ₑ ^ 2 := fun a ω =>
    setLIntegral_congr_fun measurableSet_Ioc fun r hr => by rw [min_eq_left hr.2]
  have hcl2 : ∀ ω, ∫⁻ r in Set.Ioc s t, ∑ a ∈ F, ‖ξ r ω a‖ₑ ^ 2 =
      ∫⁻ r in Set.Ioc s t, ∑ a ∈ F, ‖ξ (min r t) ω a‖ₑ ^ 2 := fun ω =>
    setLIntegral_congr_fun measurableSet_Ioc fun r hr => by simp only [min_eq_left hr.2]
  simp_rw [hcl2]
  have h2 : ∀ ω, ∫⁻ r in Set.Ioc s t, ∑ a ∈ F, ‖ξ (min r t) ω a‖ₑ ^ 2 =
      ∑ a ∈ F, ∫⁻ r in Set.Ioc s t, ‖ξ (min r t) ω a‖ₑ ^ 2 := fun ω =>
    lintegral_finset_sum _ fun a _ =>
      ((measurable_cT_integrand hξ a t).comp measurable_prodMk_right)
  simp_rw [h2]
  rw [lintegral_finset_sum]
  · refine Finset.sum_congr rfl fun a _ => ?_
    unfold cS
    exact lintegral_congr fun ω => (hcl a ω).symm
  · intro a _
    exact ((measurable_cT_integrand hξ a t).comp
      (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right' (ν := volume.restrict (Set.Ioc s t))

lemma ItoF_lintegral_sub_sq (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (F : Finset A) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {S : Set Ω} (hSm : MeasurableSet[ℱ s] S) :
    ∫⁻ ω in S, ‖ItoF P ℱ 𝔚 ξ F t ω - ItoF P ℱ 𝔚 ξ F s ω‖ₑ ^ 2 ∂P = ∑ a ∈ F, cS P ξ a S s t := by
  have hSm' : MeasurableSet S := ℱ.le s _ hSm
  have hΦ := hξ.progressiveL2 F
  have hM := isItoIntegral_itoIntegral (hW F) hΦ
  have hR := hM.restrict (hW F) hΦ hs hst hSm
  have h : ∫⁻ ω, ‖(if ω ∈ S then ItoF P ℱ 𝔚 ξ F (min t t) ω - ItoF P ℱ 𝔚 ξ F (min t s) ω else 0)‖ₑ ^ 2 ∂P =
      sqIntegralOn P (restrictFun (ξF ξ F) s t S) t := hR.lintegral_sq (hW F) (hΦ.restrictFun hSm) t
  rw [sqIntegralOn_restrictFun_eq _ hs hSm'] at h
  have e1 : ∀ ω, ‖(if ω ∈ S then ItoF P ℱ 𝔚 ξ F (min t t) ω - ItoF P ℱ 𝔚 ξ F (min t s) ω else 0)‖ₑ ^ 2 =
      S.indicator (fun ω => ‖ItoF P ℱ 𝔚 ξ F t ω - ItoF P ℱ 𝔚 ξ F s ω‖ₑ ^ 2) ω := fun ω => by
    by_cases hω : ω ∈ S <;> simp [hω, min_self, min_eq_right hst]
  simp_rw [e1] at h
  rw [lintegral_indicator hSm'] at h
  rw [h]
  have := lintegral_finset_sum_Ioc (P := P) hξ.prog F hst S
  rw [← this]
  refine lintegral_congr fun ω => ?_
  refine lintegral_congr fun r => ?_
  exact Finset.sum_coe_sort F (fun a => ‖ξ r ω a‖ₑ ^ 2)

/-- Conditional isometry for the countable Itô integral (in `ℝ≥0∞`):
`E[1_S |I_t - I_s|²] = ∑_a E[1_S ∫_s^t |ξ_a|²]`, `S ∈ ℱ_s`. -/
theorem IsItoC.lintegral_set_sub_sq (hξ : IsCtbl P ℱ ξ) (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hI : IsItoC P ℱ 𝔚 ξ I) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {S : Set Ω}
    (hSm : MeasurableSet[ℱ s] S) :
    ∫⁻ ω in S, ‖I t ω - I s ω‖ₑ ^ 2 ∂P = ∑' a, cS P ξ a S s t := by
  obtain ⟨F, hF⟩ := exists_finset_seq (A := A)
  have hSm' : MeasurableSet S := ℱ.le s _ hSm
  have hts : 0 ≤ t := hs.trans hst
  -- `L²` convergence of the restricted differences
  set Dn : ℕ → Ω → ℝ := fun n ω => S.indicator (fun ω => ItoF P ℱ 𝔚 ξ (F n) t ω - ItoF P ℱ 𝔚 ξ (F n) s ω) ω
    with hDn
  set Dinf : Ω → ℝ := S.indicator (fun ω => I t ω - I s ω) with hDinf
  have hDL2 : ∀ n, MemLp (Dn n) 2 P := fun n =>
    (((memLp_two_itoIntegral (hW (F n)) (hξ.progressiveL2 (F n)) t).sub
      (memLp_two_itoIntegral (hW (F n)) (hξ.progressiveL2 (F n)) s)).indicator hSm')
  have hDinfL2 : MemLp Dinf 2 P := ((hI.memLp hξ hW hts).sub (hI.memLp hξ hW hs)).indicator hSm'
  have hconv : Tendsto (fun n => ∫⁻ ω, ‖Dn n ω - Dinf ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    have h1 := (hI.approx t hts).comp hF
    have h2 := (hI.approx s hs).comp hF
    have hb : Tendsto (fun n => 2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ (F n) t ω - I t ω‖ₑ ^ 2 ∂P +
        2 * ∫⁻ ω, ‖-(ItoF P ℱ 𝔚 ξ (F n) s ω - I s ω)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
      simp_rw [enorm_neg]
      have := (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
        (ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le)
      fun n => ?_
    have ha := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) (F n) t
    have hb' := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) (F n) s
    calc ∫⁻ ω, ‖Dn n ω - Dinf ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, ‖(ItoF P ℱ 𝔚 ξ (F n) t ω - I t ω) + -(ItoF P ℱ 𝔚 ξ (F n) s ω - I s ω)‖ₑ ^ 2 ∂P := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ S
          · simp only [hDn, hDinf, Set.indicator_of_mem hω]
            refine le_of_eq ?_
            congr 2; ring
          · simp [hDn, hDinf, Set.indicator_of_notMem hω]
      _ ≤ _ := lintegral_enorm_sq_add_le' (ha.sub (hI.aemeasurable t)) ((hb'.sub (hI.aemeasurable s)).neg)
  have hlim := tendsto_lintegral_sq_of_L2 hDL2 hDinfL2 hconv
  have hfin : ∀ n, ∫⁻ ω, ‖Dn n ω‖ₑ ^ 2 ∂P = ∑ a ∈ F n, cS P ξ a S s t := fun n => by
    rw [← ItoF_lintegral_sub_sq hW hξ (F n) hs hst hSm, ← lintegral_indicator hSm']
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ S <;> simp [hDn, hω]
  simp_rw [hfin] at hlim
  have hsum : Tendsto (fun n => ∑ a ∈ F n, cS P ξ a S s t) atTop (𝓝 (∑' a, cS P ξ a S s t)) :=
    (ENNReal.summable.hasSum).comp hF
  have e : ∫⁻ ω, ‖Dinf ω‖ₑ ^ 2 ∂P = ∫⁻ ω in S, ‖I t ω - I s ω‖ₑ ^ 2 ∂P := by
    rw [← lintegral_indicator hSm']
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ S <;> simp [hDinf, hω]
  rw [← e]
  exact tendsto_nhds_unique hlim hsum

end CtblCond
end FragQ8

section FragR1
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section ProdMart
variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]

/-- The product filtration `ℱ_t = σ(ℱ¹_t × ℱ²_t) ∨ nullSets`. -/
def prodFiltration (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) (ℱ₁ : Filtration ℝ m₁)
    (ℱ₂ : Filtration ℝ m₂) : Filtration ℝ (inferInstance : MeasurableSpace (Ω₁ × Ω₂)) where
  seq t := (MeasurableSpace.comap Prod.fst (ℱ₁ t) ⊔ MeasurableSpace.comap Prod.snd (ℱ₂ t)) ⊔
    nullSets (P₁.prod P₂)
  mono' := fun s t hst => sup_le_sup_right (sup_le_sup (MeasurableSpace.comap_mono (ℱ₁.mono hst))
    (MeasurableSpace.comap_mono (ℱ₂.mono hst))) _
  le' := fun t => sup_le (sup_le ((MeasurableSpace.comap_mono (ℱ₁.le t)).trans measurable_fst.comap_le)
    ((MeasurableSpace.comap_mono (ℱ₂.le t)).trans measurable_snd.comap_le)) (nullSets_le _)

lemma setIntegral_prodMul_eq {Y Y' : Ω₁ → ℝ} {Z Z' : Ω₂ → ℝ} (hY : Integrable Y P₁)
    (hY' : Integrable Y' P₁) (hZ : Integrable Z P₂) (hZ' : Integrable Z' P₂) {A₁ : Set Ω₁}
    {A₂ : Set Ω₂} (h1 : ∫ x in A₁, Y x ∂P₁ = ∫ x in A₁, Y' x ∂P₁)
    (h2 : ∫ x in A₂, Z x ∂P₂ = ∫ x in A₂, Z' x ∂P₂) :
    ∫ p in A₁ ×ˢ A₂, Y p.1 * Z p.2 ∂(P₁.prod P₂) = ∫ p in A₁ ×ˢ A₂, Y' p.1 * Z' p.2 ∂(P₁.prod P₂) := by
  rw [setIntegral_prod_mul, setIntegral_prod_mul, h1, h2]

set_option warn.classDefReducibility false in
/-- The σ-algebra `σ(ℱ¹_s × ℱ²_s)` of the product. -/
def prodSigma (ℱ₁ : Filtration ℝ m₁) (ℱ₂ : Filtration ℝ m₂) (s : ℝ) : MeasurableSpace (Ω₁ × Ω₂) :=
  MeasurableSpace.comap Prod.fst (ℱ₁ s) ⊔ MeasurableSpace.comap Prod.snd (ℱ₂ s)

lemma prodSigma_le (ℱ₁ : Filtration ℝ m₁) (ℱ₂ : Filtration ℝ m₂) (s : ℝ) :
    prodSigma ℱ₁ ℱ₂ s ≤ (inferInstance : MeasurableSpace (Ω₁ × Ω₂)) :=
  sup_le ((MeasurableSpace.comap_mono (ℱ₁.le s)).trans measurable_fst.comap_le)
    ((MeasurableSpace.comap_mono (ℱ₂.le s)).trans measurable_snd.comap_le)

/-- Two integrable functions with equal integrals over all measurable rectangles of
`ℱ¹_s × ℱ²_s` have equal integrals over all sets of the product σ-algebra. -/
lemma setIntegral_eq_of_rectangles (ℱ₁ : Filtration ℝ m₁) (ℱ₂ : Filtration ℝ m₂) (s : ℝ)
    {f g : Ω₁ × Ω₂ → ℝ} (hf : Integrable f (P₁.prod P₂))
    (hg : Integrable g (P₁.prod P₂))
    (hrect : ∀ A₁ A₂, MeasurableSet[ℱ₁ s] A₁ → MeasurableSet[ℱ₂ s] A₂ →
      ∫ p in A₁ ×ˢ A₂, f p ∂(P₁.prod P₂) = ∫ p in A₁ ×ˢ A₂, g p ∂(P₁.prod P₂))
    {S : Set (Ω₁ × Ω₂)} (hS : MeasurableSet[prodSigma ℱ₁ ℱ₂ s] S) :
    ∫ p in S, f p ∂(P₁.prod P₂) = ∫ p in S, g p ∂(P₁.prod P₂) := by
  have h𝒟le := prodSigma_le ℱ₁ ℱ₂ s
  let p : Set (Set (Ω₁ × Ω₂)) :=
    {S | ∃ A₁ A₂, MeasurableSet[ℱ₁ s] A₁ ∧ MeasurableSet[ℱ₂ s] A₂ ∧ S = A₁ ×ˢ A₂}
  have hπ : IsPiSystem p := by
    rintro _ ⟨a, b, ha, hb, rfl⟩ _ ⟨a', b', ha', hb', rfl⟩ _
    exact ⟨a ∩ a', b ∩ b', @MeasurableSet.inter _ (ℱ₁ s) _ _ ha ha',
      @MeasurableSet.inter _ (ℱ₂ s) _ _ hb hb', by ext; simp; tauto⟩
  have hrectS : ∀ a b, MeasurableSet[ℱ₁ s] a → MeasurableSet[ℱ₂ s] b →
      MeasurableSet[prodSigma ℱ₁ ℱ₂ s] (a ×ˢ b) := by
    intro a b ha hb
    have e : a ×ˢ b = Prod.fst ⁻¹' a ∩ Prod.snd ⁻¹' b := by ext; simp
    rw [e]
    exact @MeasurableSet.inter _ (prodSigma ℱ₁ ℱ₂ s) _ _
      (le_sup_left (a := MeasurableSpace.comap Prod.fst (ℱ₁ s))
        (b := MeasurableSpace.comap Prod.snd (ℱ₂ s)) _ ⟨a, ha, rfl⟩)
      (le_sup_right (a := MeasurableSpace.comap Prod.fst (ℱ₁ s))
        (b := MeasurableSpace.comap Prod.snd (ℱ₂ s)) _ ⟨b, hb, rfl⟩)
  have hgen : prodSigma ℱ₁ ℱ₂ s = MeasurableSpace.generateFrom p := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact MeasurableSpace.measurableSet_generateFrom ⟨a, Set.univ, ha,
          @MeasurableSet.univ _ (ℱ₂ s), by ext; simp⟩
      · rintro _ ⟨b, hb, rfl⟩
        exact MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, b,
          @MeasurableSet.univ _ (ℱ₁ s), hb, by ext; simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, b, ha, hb, rfl⟩
      exact hrectS a b ha hb
  have htot : ∫ q, f q ∂(P₁.prod P₂) = ∫ q, g q ∂(P₁.prod P₂) := by
    have := hrect Set.univ Set.univ (@MeasurableSet.univ _ (ℱ₁ s)) (@MeasurableSet.univ _ (ℱ₂ s))
    simpa using this
  refine MeasurableSpace.induction_on_inter (m := prodSigma ℱ₁ ℱ₂ s)
    (C := fun S _ => ∫ x in S, f x ∂(P₁.prod P₂) = ∫ x in S, g x ∂(P₁.prod P₂)) hgen hπ ?_ ?_ ?_ ?_
    S hS
  · simp
  · rintro _ ⟨a, b, ha, hb, rfl⟩
    exact hrect a b ha hb
  · intro t ht h
    have ht' : MeasurableSet t := h𝒟le _ ht
    have e1 := integral_add_compl ht' hf
    have e2 := integral_add_compl ht' hg
    linarith
  · intro u hdisj hu h
    have hu' : ∀ i, MeasurableSet (u i) := fun i => h𝒟le _ (hu i)
    rw [integral_iUnion hu' hdisj hf.integrableOn, integral_iUnion hu' hdisj hg.integrableOn]
    exact tsum_congr h

/-- The product of independent martingales (with respect to their own filtrations) is a
martingale for the product filtration. -/
theorem martingale_mul_prod (ℱ₁ : Filtration ℝ m₁) (ℱ₂ : Filtration ℝ m₂)
    {Y : ℝ → Ω₁ → ℝ} {Z : ℝ → Ω₂ → ℝ} (hY : Martingale Y ℱ₁ P₁) (hZ : Martingale Z ℱ₂ P₂) :
    Martingale (fun t (p : Ω₁ × Ω₂) => Y t p.1 * Z t p.2) (prodFiltration P₁ P₂ ℱ₁ ℱ₂)
      (P₁.prod P₂) := by
  have hint : ∀ t, Integrable (fun p : Ω₁ × Ω₂ => Y t p.1 * Z t p.2) (P₁.prod P₂) := fun t =>
    (hY.integrable t).mul_prod (hZ.integrable t)
  have hsm : ∀ t, StronglyMeasurable[prodSigma ℱ₁ ℱ₂ t]
      (fun p : Ω₁ × Ω₂ => Y t p.1 * Z t p.2) := fun t => by
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable[prodSigma ℱ₁ ℱ₂ t] (fun p : Ω₁ × Ω₂ => Y t p.1) :=
      ((hY.1 t).measurable.comp (comap_measurable (Prod.fst : Ω₁ × Ω₂ → Ω₁))).mono le_sup_left le_rfl
    have h2 : Measurable[prodSigma ℱ₁ ℱ₂ t] (fun p : Ω₁ × Ω₂ => Z t p.2) :=
      ((hZ.1 t).measurable.comp (comap_measurable (Prod.snd : Ω₁ × Ω₂ → Ω₂))).mono le_sup_right le_rfl
    exact h1.mul h2
  refine ⟨fun t => (hsm t).mono le_sup_left, fun s r hsr => ?_⟩
  have e1 : (P₁.prod P₂)[fun p : Ω₁ × Ω₂ => Y r p.1 * Z r p.2 | prodFiltration P₁ P₂ ℱ₁ ℱ₂ s]
      =ᵐ[P₁.prod P₂] (P₁.prod P₂)[fun p : Ω₁ × Ω₂ => Y r p.1 * Z r p.2 | prodSigma ℱ₁ ℱ₂ s] :=
    condExp_sup_nullSets (prodSigma_le ℱ₁ ℱ₂ s) _
  refine e1.trans ?_
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (prodSigma_le ℱ₁ ℱ₂ s) (hint r)
    (fun S _ _ => (hint s).integrableOn) (fun S hS _ => ?_) (hsm s).aestronglyMeasurable
  exact setIntegral_eq_of_rectangles ℱ₁ ℱ₂ s (hint s) (hint r) (fun A₁ A₂ hA₁ hA₂ =>
    setIntegral_prodMul_eq (hY.integrable s) (hY.integrable r) (hZ.integrable s) (hZ.integrable r)
      (hY.setIntegral_eq hsr hA₁) (hZ.setIntegral_eq hsr hA₂)) hS

end ProdMart
end FragR1

section FragR2
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section InfWiener
universe u
variable (ι : Type u)

/-- The law of a family of independent Wiener sequences indexed by `ι`. -/
abbrev wMeasure : Measure (ι → WienerSeq) := Measure.infinitePi fun _ : ι => wienerMeasure

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by all coordinate paths up to time `τ`, with the null sets. -/
def wSigma (τ : ℝ) : MeasurableSpace (ι → WienerSeq) :=
  (⨆ (r : ℝ≥0) (_ : (r : ℝ) ≤ τ) (i : ι),
    MeasurableSpace.comap (fun ω : ι → WienerSeq => wienerPath r (ω i)) inferInstance) ⊔
    nullSets (wMeasure ι)

lemma wSigma_mono {ι : Type u} {s t : ℝ} (hst : s ≤ t) : wSigma ι s ≤ wSigma ι t := by
  unfold wSigma
  refine sup_le_sup_right ?_ _
  refine iSup_le fun r => iSup_le fun hr => ?_
  exact le_iSup_of_le r (le_iSup_of_le (hr.trans hst) le_rfl)

lemma wSigma_le {ι : Type u} (τ : ℝ) : wSigma ι τ ≤ (inferInstance : MeasurableSpace (ι → WienerSeq)) := by
  unfold wSigma
  refine sup_le (iSup_le fun r => iSup_le fun _ => iSup_le fun i => ?_) (nullSets_le _)
  have h : Measurable fun ω : ι → WienerSeq => wienerPath r (ω i) :=
    (measurable_wienerPath r).comp (measurable_pi_apply i)
  exact h.comap_le

/-- The filtration generated by the family of independent Wiener paths. -/
def wFiltration : Filtration ℝ (inferInstance : MeasurableSpace (ι → WienerSeq)) where
  seq := wSigma ι
  mono' := fun _ _ hst => wSigma_mono (ι := ι) hst
  le' := wSigma_le (ι := ι)

variable {ι}

lemma wFiltration_complete : IsCompleteFiltration (wMeasure ι) (wFiltration ι) := by
  intro t s hs hP
  have h1 : MeasurableSet[nullSets (wMeasure ι)] s :=
    MeasurableSpace.measurableSet_generateFrom ⟨hs, hP⟩
  exact (le_sup_right : nullSets (wMeasure ι) ≤ wSigma ι t) s h1

lemma comap_wCoord_le (t : ℝ≥0) (τ : ℝ) (hτ : (t : ℝ) ≤ τ) (i : ι) :
    MeasurableSpace.comap (fun ω : ι → WienerSeq => wienerPath t (ω i)) inferInstance ≤
      wFiltration ι τ :=
  (le_iSup_of_le t (le_iSup_of_le hτ (le_iSup (f := fun i : ι => MeasurableSpace.comap (fun ω : ι → WienerSeq => wienerPath t (ω i)) inferInstance) i)) :
      MeasurableSpace.comap (fun ω : ι → WienerSeq => wienerPath t (ω i)) inferInstance ≤ _).trans
    (le_sup_left : _ ≤ wSigma ι τ)

lemma measurable_wCoord (t : ℝ≥0) (τ : ℝ) (hτ : (t : ℝ) ≤ τ) (i : ι) :
    Measurable[wFiltration ι τ] (fun ω : ι → WienerSeq => wienerPath t (ω i)) :=
  Measurable.of_comap_le (comap_wCoord_le t τ hτ i)

lemma comap_fun_le {Ξ : Type*} {M : MeasurableSpace Ξ} {F : Type*} {β : F → Type*}
    [∀ k, MeasurableSpace (β k)] (g : Ξ → ∀ k, β k)
    (h : ∀ k, MeasurableSpace.comap (fun ω => g ω k) inferInstance ≤ M) :
    MeasurableSpace.comap g inferInstance ≤ M := by
  show MeasurableSpace.comap g MeasurableSpace.pi ≤ M
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, iSup_le_iff]
  intro k
  rw [MeasurableSpace.comap_comp]
  exact h k

lemma comap_wienerPath_le (t : ℝ≥0) (i : ι) :
    MeasurableSpace.comap (fun ω : ι → WienerSeq => wienerPath t (ω i)) inferInstance ≤
      MeasurableSpace.comap (fun ω : ι → WienerSeq => ω i) inferInstance := by
  rw [show (fun ω : ι → WienerSeq => wienerPath t (ω i)) =
    (fun x : WienerSeq => wienerPath t x) ∘ (fun ω : ι → WienerSeq => ω i) from rfl,
    ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_wienerPath t).comap_le

lemma isBrownianFiltration_wFiltration (F : Finset ι) :
    IsBrownianFiltration (wMeasure ι) (wFiltration ι)
      (fun t ω (i : F) => wienerPath t (ω i)) := by
  classical
  set ν : Measure (ι → WienerSeq) := wMeasure ι with hν
  set W : ℝ≥0 → (ι → WienerSeq) → F → ℝ := fun t ω i => wienerPath t (ω i) with hWdef
  have hW : ∀ t, Measurable (W t) := fun t =>
    Measurable.of_eval fun i => (measurable_wienerPath t).comp ((measurable_pi_apply (i : ι)))
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => funext fun k => wienerPath_zero _
  have hWc : ∀ ω, Continuous fun t => W t ω := fun ω =>
    continuous_pi fun k => continuous_wienerPath _
  have hev : ∀ i : ι, MeasurePreserving (fun ω : ι → WienerSeq => ω i) ν wienerMeasure :=
    fun i => measurePreserving_eval_infinitePi (fun _ : ι => wienerMeasure) i
  have hB : ∀ k : F, IsBrownianReal (fun t ω => W t ω k) ν := fun k =>
    IsBrownianReal.comp_measurePreserving (hev k) isPreBrownianReal_wienerPath
      continuous_wienerPath
  have hpath : Measurable fun (ω : WienerSeq) (t : ℝ≥0) => wienerPath t ω :=
    Measurable.of_eval measurable_wienerPath
  have hind0 : iIndepFun (fun (i : ι) (ω : ι → WienerSeq) => fun t : ℝ≥0 => wienerPath t (ω i)) ν :=
    iIndepFun_infinitePi (P := fun _ : ι => wienerMeasure)
      (X := fun _ => fun ω t => wienerPath t ω) fun _ => hpath
  have hind : iIndepFun (fun (k : F) ω => fun t : ℝ≥0 => W t ω k) ν :=
    hind0.precomp (g := fun k : F => (k : ι)) Subtype.val_injective
  set X₀ : (ι → WienerSeq) → ({i // i ∉ F} → WienerSeq) := fun ω i => ω i.1 with hX₀def
  have hX₀ : Measurable X₀ := measurable_pi_iff.2 fun i => measurable_pi_apply i.1
  have hind' : iIndep (fun i : ι => MeasurableSpace.comap (fun ω : ι → WienerSeq => ω i) inferInstance) ν := by
    have := iIndepFun_infinitePi (P := fun _ : ι => wienerMeasure) (X := fun _ => (id : WienerSeq → WienerSeq))
      (fun _ => measurable_id)
    exact this
  have hX₀W : IndepFun X₀ (fun ω => fun t => W t ω) ν := by
    have h1 := indep_iSup_of_disjoint (fun i => (measurable_pi_apply i).comap_le) hind'
      (S := {i | i ∉ F}) (T := (F : Set ι)) (by
        rw [Set.disjoint_left]; intro a ha hb; exact ha hb)
    rw [IndepFun_iff_Indep]
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left h1 ?_) ?_
    · refine comap_fun_le X₀ fun k => ?_
      exact le_iSup₂_of_le k.1 k.2 le_rfl
    · refine comap_fun_le _ fun t => comap_fun_le _ fun k => ?_
      exact (comap_wienerPath_le t (k : ι)).trans (le_iSup₂_of_le (k : ι) k.2 le_rfl)
  have hG := isBrownianFiltration_generated ν W hW hB hind hW0 hWc X₀ hX₀ hX₀W
  refine hG.of_le_of_adapted (fun u => ?_) wFiltration_complete (fun u => ?_)
  · refine sup_le (iSup_le fun r => iSup_le fun hr => iSup_le fun i => ?_) le_sup_right
    by_cases hi : i ∈ F
    · refine le_trans ?_ ((le_iSup₂_of_le r hr le_rfl : MeasurableSpace.comap (W r) inferInstance ≤ _).trans
        (le_sup_right.trans le_sup_left))
      rw [show (fun ω : ι → WienerSeq => wienerPath r (ω i)) =
        (fun v : F → ℝ => v ⟨i, hi⟩) ∘ W r from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
    · refine le_trans ?_ (le_sup_left.trans le_sup_left)
      refine (comap_wienerPath_le r i).trans ?_
      rw [show (fun ω : ι → WienerSeq => ω i) =
        (fun v : {i // i ∉ F} → WienerSeq => v ⟨i, hi⟩) ∘ X₀ from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le
  · refine Measurable.of_comap_le (comap_fun_le _ fun k => ?_)
    exact comap_wCoord_le (ι := ι) u u le_rfl (k : ι)
end InfWiener
end FragR2

section FragR3
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section ProdBM
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {κ : Type*} [Countable κ] {W : ℝ≥0 → Ω → κ → ℝ}

lemma IsCylindricalBrownian.martingale_coord (hW : IsCylindricalBrownian P ℱ W) (k : κ) :
    Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k) ℱ P := by
  have h := (hW {k}).martingale ⟨k, by simp⟩
  exact h

lemma IsCylindricalBrownian.martingale_mul_sub (hW : IsCylindricalBrownian P ℱ W) (k l : κ) :
    Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k * ofNNRealTime W t ω l -
      if k = l then max t 0 else 0) ℱ P := by
  by_cases hkl : k = l
  · subst hkl
    have h := (hW {k}).martingale_sq_sub ⟨k, by simp⟩
    simpa [sq] using h
  · have h := (hW {k, l}).martingale_mul (k := ⟨k, by simp⟩) (l := ⟨l, by simp⟩)
      (fun h => hkl (congrArg Subtype.val h))
    simpa [hkl] using h

lemma IsCylindricalBrownian.measurable_coord (hW : IsCylindricalBrownian P ℱ W) (t : ℝ≥0) (k : κ) :
    Measurable[ℱ t] (fun ω => W t ω k) := by
  have h := (hW {k}).adapted t
  exact (measurable_pi_apply (⟨k, by simp⟩ : ({k} : Finset κ))).comp h

end ProdBM

section ProdBM2
open Classical

variable {Ω₁ Ω₂ : Type*} {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂}
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
  {ℱ₁ : Filtration ℝ m₁} {ℱ₂ : Filtration ℝ m₂} {κ ι : Type*} [Countable κ] [Countable ι]
  {W₁ : ℝ≥0 → Ω₁ → κ → ℝ} {W₂ : ℝ≥0 → Ω₂ → ι → ℝ}

/-- The combined family on the index set `κ ⊕ ι`. -/
def sumFam (W₁ : ℝ≥0 → Ω₁ → κ → ℝ) (W₂ : ℝ≥0 → Ω₂ → ι → ℝ) : ℝ≥0 → Ω₁ × Ω₂ → κ ⊕ ι → ℝ :=
  fun t p a => Sum.elim (fun k => W₁ t p.1 k) (fun i => W₂ t p.2 i) a

lemma comap_fst_le_prod {f : Ω₁ → ℝ} {t : ℝ} (hf : Measurable[ℱ₁ t] f) :
    MeasurableSpace.comap (fun p : Ω₁ × Ω₂ => f p.1) inferInstance ≤
      prodFiltration P₁ P₂ ℱ₁ ℱ₂ t := by
  rw [show (fun p : Ω₁ × Ω₂ => f p.1) = f ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
  exact (MeasurableSpace.comap_mono hf.comap_le).trans (le_sup_left.trans le_sup_left)

lemma comap_snd_le_prod {f : Ω₂ → ℝ} {t : ℝ} (hf : Measurable[ℱ₂ t] f) :
    MeasurableSpace.comap (fun p : Ω₁ × Ω₂ => f p.2) inferInstance ≤
      prodFiltration P₁ P₂ ℱ₁ ℱ₂ t := by
  rw [show (fun p : Ω₁ × Ω₂ => f p.2) = f ∘ Prod.snd from rfl, ← MeasurableSpace.comap_comp]
  exact (MeasurableSpace.comap_mono hf.comap_le).trans (le_sup_right.trans le_sup_left)

theorem isCylindricalBrownian_prod (h₁ : IsCylindricalBrownian P₁ ℱ₁ W₁)
    (h₂ : IsCylindricalBrownian P₂ ℱ₂ W₂) :
    IsCylindricalBrownian (P₁.prod P₂) (prodFiltration P₁ P₂ ℱ₁ ℱ₂) (sumFam W₁ W₂) := by
  intro s
  have hmart : ∀ a : κ ⊕ ι, Martingale (fun (t : ℝ) (p : Ω₁ × Ω₂) =>
      ofNNRealTime (sumFam W₁ W₂) t p a) (prodFiltration P₁ P₂ ℱ₁ ℱ₂) (P₁.prod P₂) := by
    intro a
    rcases a with k | i
    · have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ (h₁.martingale_coord k)
        (martingale_const ℱ₂ P₂ (1 : ℝ))
      convert this using 2 with t p
      simp [sumFam]
    · have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ (martingale_const ℱ₁ P₁ (1 : ℝ))
        (h₂.martingale_coord i)
      convert this using 2 with t p
      simp [sumFam]
  have hqv : ∀ a b : κ ⊕ ι, Martingale (fun (t : ℝ) (p : Ω₁ × Ω₂) =>
      ofNNRealTime (sumFam W₁ W₂) t p a * ofNNRealTime (sumFam W₁ W₂) t p b -
        if a = b then max t 0 else 0) (prodFiltration P₁ P₂ ℱ₁ ℱ₂) (P₁.prod P₂) := by
    intro a b
    rcases a with k | i <;> rcases b with l | j
    · have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ (h₁.martingale_mul_sub k l)
        (martingale_const ℱ₂ P₂ (1 : ℝ))
      convert this using 2 with t p
      simp [sumFam]
    · have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ (h₁.martingale_coord k)
        (h₂.martingale_coord j)
      convert this using 2 with t p
      simp [sumFam]
    · have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ (h₁.martingale_coord l)
        (h₂.martingale_coord i)
      convert this using 2 with t p
      simp [sumFam, mul_comm]
    · have := martingale_mul_prod (P₁ := P₁) (P₂ := P₂) ℱ₁ ℱ₂ (martingale_const ℱ₁ P₁ (1 : ℝ))
        (h₂.martingale_mul_sub i j)
      convert this using 2 with t p
      simp [sumFam]
  refine levy_characterization (P₁.prod P₂) (prodFiltration P₁ P₂ ℱ₁ ℱ₂) ?_ _ ?_ ?_ ?_ ?_ ?_
  · intro t S hS hP
    have h1 : MeasurableSet[nullSets (P₁.prod P₂)] S :=
      MeasurableSpace.measurableSet_generateFrom ⟨hS, hP⟩
    exact (le_sup_right : nullSets (P₁.prod P₂) ≤ prodFiltration P₁ P₂ ℱ₁ ℱ₂ t) S h1
  · intro t
    refine Measurable.of_comap_le (comap_fun_le _ fun a => ?_)
    rcases a with ⟨a | i, ha⟩
    · exact comap_fst_le_prod (h₁.measurable_coord t a)
    · exact comap_snd_le_prod (h₂.measurable_coord t i)
  · intro p
    funext a
    rcases a with ⟨a | i, ha⟩
    · have := congrFun ((h₁ {a}).zero p.1) ⟨a, by simp⟩
      simpa [sumFam] using this
    · have := congrFun ((h₂ {i}).zero p.2) ⟨i, by simp⟩
      simpa [sumFam] using this
  · intro p
    refine continuous_pi fun a => ?_
    rcases a with ⟨a | i, ha⟩
    · exact (continuous_apply (⟨a, by simp⟩ : ({a} : Finset κ))).comp ((h₁ {a}).cont p.1)
    · exact (continuous_apply (⟨i, by simp⟩ : ({i} : Finset ι))).comp ((h₂ {i}).cont p.2)
  · intro a
    exact hmart a.1
  · intro a b
    have := hqv a.1 b.1
    convert this using 3
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (congrArg Subtype.val hab)]; rfl
    · rw [if_neg hab, if_neg (fun h => hab (Subtype.ext h))]; rfl

end ProdBM2
end FragR3

section FragR4
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CtblCalc
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {A : Type*} {ξ ξ' : ℝ → Ω → A → ℝ}

lemma measurable_inner_Ioc (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (a : A) (s t : ℝ) :
    Measurable (fun ω => ∫⁻ r in Set.Ioc s t, ‖ξ r ω a‖ₑ ^ 2) := by
  have h := ((measurable_cT_integrand hξ a t).comp
    (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right' (ν := volume.restrict (Set.Ioc s t))
  have e : (fun ω => ∫⁻ r in Set.Ioc s t, ‖ξ r ω a‖ₑ ^ 2) =
      fun ω => ∫⁻ r in Set.Ioc s t, ‖ξ (min r t) ω a‖ₑ ^ 2 := by
    funext ω
    exact setLIntegral_congr_fun measurableSet_Ioc fun r hr => by rw [min_eq_left hr.2]
  rw [e]
  exact h

lemma measurable_inner_Icc (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (a : A) (T : ℝ) :
    Measurable (fun ω => ∫⁻ r in Set.Icc 0 T, ‖ξ r ω a‖ₑ ^ 2) := by
  have h := ((measurable_cT_integrand hξ a T).comp
    (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 T))
  have e : (fun ω => ∫⁻ r in Set.Icc 0 T, ‖ξ r ω a‖ₑ ^ 2) =
      fun ω => ∫⁻ r in Set.Icc 0 T, ‖ξ (min r T) ω a‖ₑ ^ 2 := by
    funext ω
    exact setLIntegral_congr_fun measurableSet_Icc fun r hr => by rw [min_eq_left hr.2]
  rw [e]
  exact h

lemma measurable_slice_enorm_sq (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (a : A) (ω : Ω) :
    Measurable (fun r => ‖ξ r ω a‖ₑ ^ 2) :=
  (measurable_slice (hξ a) ω).enorm.pow_const 2

lemma cT_add_le (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a))
    (hξ' : ∀ a, IsProgressive ℱ (fun r ω => ξ' r ω a)) (a : A) (T : ℝ) :
    cT P (fun r ω a => ξ r ω a + ξ' r ω a) a T ≤ 2 * cT P ξ a T + 2 * cT P ξ' a T := by
  unfold cT
  have hm := measurable_inner_Icc hξ a T
  have hm' := measurable_inner_Icc hξ' a T
  calc ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ‖ξ s ω a + ξ' s ω a‖ₑ ^ 2) ∂P
      ≤ ∫⁻ ω, (2 * (∫⁻ s in Set.Icc 0 T, ‖ξ s ω a‖ₑ ^ 2) + 2 * (∫⁻ s in Set.Icc 0 T, ‖ξ' s ω a‖ₑ ^ 2)) ∂P := by
        refine lintegral_mono fun ω => ?_
        calc ∫⁻ s in Set.Icc 0 T, ‖ξ s ω a + ξ' s ω a‖ₑ ^ 2
            ≤ ∫⁻ s in Set.Icc 0 T, (2 * ‖ξ s ω a‖ₑ ^ 2 + 2 * ‖ξ' s ω a‖ₑ ^ 2) :=
              lintegral_mono fun s => enorm_add_sq_le _ _
          _ = _ := by
              rw [lintegral_add_left ((measurable_slice_enorm_sq hξ a ω).const_mul 2),
                lintegral_const_mul _ (measurable_slice_enorm_sq hξ a ω),
                lintegral_const_mul _ (measurable_slice_enorm_sq hξ' a ω)]
    _ = _ := by
        rw [lintegral_add_left (hm.const_mul 2), lintegral_const_mul _ hm,
          lintegral_const_mul _ hm']

lemma IsCtbl.add (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ') :
    IsCtbl P ℱ (fun r ω a => ξ r ω a + ξ' r ω a) := by
  refine ⟨fun a => (hξ.prog a).add (hξ'.prog a), fun T => ?_⟩
  refine ne_top_of_le_ne_top (b := ∑' a, (2 * cT P ξ a T + 2 * cT P ξ' a T)) ?_
    (ENNReal.tsum_le_tsum fun a => cT_add_le hξ.prog hξ'.prog a T)
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num) (hξ.sq T),
    ENNReal.mul_ne_top (by norm_num) (hξ'.sq T)⟩

lemma IsCtbl.mul_bdd (hξ : IsCtbl P ℱ ξ) {w : ℝ → Ω → ℝ} (hw : IsProgressive ℱ w) {C : ℝ}
    (hC : ∀ r ω, |w r ω| ≤ C) : IsCtbl P ℱ (fun r ω a => w r ω * ξ r ω a) := by
  refine ⟨fun a => hw.mul (hξ.prog a), fun T => ?_⟩
  have hle : ∀ a, cT P (fun r ω a => w r ω * ξ r ω a) a T ≤ ‖C‖ₑ ^ 2 * cT P ξ a T := by
    intro a
    unfold cT
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun ω => ?_
    rw [← lintegral_const_mul _ (measurable_slice_enorm_sq hξ.prog a ω)]
    refine lintegral_mono fun s => ?_
    rw [enorm_mul, mul_pow]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using (hC s ω).trans (le_abs_self C))
  refine ne_top_of_le_ne_top (b := ∑' a, ‖C‖ₑ ^ 2 * cT P ξ a T) ?_ (ENNReal.tsum_le_tsum hle)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top (by simp) (hξ.sq T)

lemma tsum_cS_eq [Countable A] (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) {S : Set Ω}
    (s t : ℝ) :
    ∑' a, cS P ξ a S s t = ∫⁻ ω in S, (∫⁻ r in Set.Ioc s t, ∑' a, ‖ξ r ω a‖ₑ ^ 2) ∂P := by
  unfold cS
  rw [← lintegral_tsum (fun a => (measurable_inner_Ioc hξ a s t).aemeasurable)]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_tsum (fun a => (measurable_slice_enorm_sq hξ a ω).aemeasurable)]

lemma measurable_inner_set (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (a : A) {R : Set ℝ}
    (hR : MeasurableSet R) {T : ℝ} (hRT : R ⊆ Set.Iic T) :
    Measurable (fun ω => ∫⁻ r in R, ‖ξ r ω a‖ₑ ^ 2) := by
  have h := ((measurable_cT_integrand hξ a T).comp
    (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right' (ν := volume.restrict R)
  have e : (fun ω => ∫⁻ r in R, ‖ξ r ω a‖ₑ ^ 2) =
      fun ω => ∫⁻ r in R, ‖ξ (min r T) ω a‖ₑ ^ 2 := by
    funext ω
    exact setLIntegral_congr_fun hR fun r hr => by rw [min_eq_left (hRT hr)]
  rw [e]
  exact h

lemma tsum_lintegral_set_eq [Countable A] (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a))
    {S : Set Ω} {R : Set ℝ} (hR : MeasurableSet R) {T : ℝ} (hRT : R ⊆ Set.Iic T) :
    ∑' a, ∫⁻ ω in S, (∫⁻ r in R, ‖ξ r ω a‖ₑ ^ 2) ∂P =
      ∫⁻ ω in S, (∫⁻ r in R, ∑' a, ‖ξ r ω a‖ₑ ^ 2) ∂P := by
  rw [← lintegral_tsum (fun a => (measurable_inner_set hξ a hR hRT).aemeasurable)]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_tsum (fun a => (measurable_slice_enorm_sq hξ a ω).aemeasurable)]

lemma enorm_tsum_sq_of_hasSum {f : A → ℝ} {c : ℝ} (h : HasSum (fun a => f a ^ 2) c) :
    ∑' a, ‖f a‖ₑ ^ 2 = ENNReal.ofReal c := by
  have h0 : 0 ≤ c := h.nonneg fun a => sq_nonneg _
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) h.summable]
  exact tsum_congr fun a => (enorm_sq_eq_ofReal _)

lemma lintegral_ofReal_ne_top [IsProbabilityMeasure P] [Countable A] (hξ : IsCtbl P ℱ ξ) {g : ℝ → ℝ}
    (hg : ∀ r ω, ∑' a, ‖ξ r ω a‖ₑ ^ 2 = ENNReal.ofReal (g r)) (T : ℝ) :
    ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (g r) ≠ ⊤ := by
  have h := hξ.sq T
  unfold cT at h
  have e := tsum_lintegral_set_eq (S := Set.univ) (P := P) hξ.prog measurableSet_Icc
    (fun r hr => hr.2 : Set.Icc 0 T ⊆ Set.Iic T)
  simp only [Measure.restrict_univ] at e
  rw [e] at h
  simpa [hg] using h

end CtblCalc

section SqMart
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ ξ' : ℝ → Ω → A → ℝ}
  {I I' : ℝ → Ω → ℝ}

/-- The deterministic bracket `∫_0^t g`. -/
def Gint (g : ℝ → ℝ) (t : ℝ) : ℝ := (∫⁻ r in Set.Ioc 0 t, ENNReal.ofReal (g r)).toReal

lemma Gint_of_nonpos (g : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0) : Gint g t = 0 := by
  simp [Gint, Set.Ioc_eq_empty (not_lt.2 ht)]

lemma Gint_sub {g : ℝ → ℝ} (hfin : ∀ T, ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (g r) ≠ ⊤) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    Gint g t - Gint g s = (∫⁻ r in Set.Ioc s t, ENNReal.ofReal (g r)).toReal := by
  have hsplit : (∫⁻ r in Set.Ioc 0 t, ENNReal.ofReal (g r)) =
      (∫⁻ r in Set.Ioc 0 s, ENNReal.ofReal (g r)) + (∫⁻ r in Set.Ioc s t, ENNReal.ofReal (g r)) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hs hst, lintegral_union measurableSet_Ioc
      (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  have h1 : ∫⁻ r in Set.Ioc 0 s, ENNReal.ofReal (g r) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin t) (lintegral_mono_set (fun r hr => ⟨hr.1.le, hr.2.trans hst⟩))
  have h2 : ∫⁻ r in Set.Ioc s t, ENNReal.ofReal (g r) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfin t) (lintegral_mono_set (fun r hr => ⟨hs.trans hr.1.le, hr.2⟩))
  unfold Gint
  rw [hsplit, ENNReal.toReal_add h1 h2]
  ring

theorem IsItoC.martingale_sq_sub (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hI : IsItoC P ℱ 𝔚 ξ I) {g : ℝ → ℝ}
    (hg : ∀ r ω, ∑' a, ‖ξ r ω a‖ₑ ^ 2 = ENNReal.ofReal (g r)) :
    Martingale (fun t ω => I t ω ^ 2 - Gint g t) ℱ P := by
  have hfin := lintegral_ofReal_ne_top hξ hg
  have hM := hI.martingale hξ hW
  have hM2 : ∀ t, MemLp (I t) 2 P := fun t => by
    rcases le_or_gt 0 t with ht | ht
    · exact hI.memLp hξ hW ht
    · have : I t = fun _ => 0 := funext fun ω => hI.zero t ht.le ω
      rw [this]; exact MemLp.zero
  refine martingale_sq_sub_aux (A := fun t _ => Gint g t) hM hM2
    (fun t => measurable_const) (fun t => integrable_const _)
    (fun t ht ω => by simp [hI.zero t ht ω, Gint_of_nonpos g ht]) ?_
  intro s t hs hst
  have hc : P[fun ω => Gint g t - Gint g s | ℱ s] = fun _ => Gint g t - Gint g s :=
    condExp_const (ℱ.le s) _
  rw [hc]
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    (((hM2 t).sub (hM2 s)).integrable_sq) (fun S _ _ => integrable_const _ |>.integrableOn)
    (fun S hS _ => ?_) (aestronglyMeasurable_const)
  have hSm : MeasurableSet S := ℱ.le s S hS
  have h1 := hI.lintegral_set_sub_sq hξ hW hs hst hS
  rw [tsum_cS_eq hξ.prog (S := S) s t] at h1
  have e2 : ∫⁻ ω in S, (∫⁻ r in Set.Ioc s t, ∑' a, ‖ξ r ω a‖ₑ ^ 2) ∂P =
      P S * ∫⁻ r in Set.Ioc s t, ENNReal.ofReal (g r) := by
    simp_rw [hg]
    rw [lintegral_const, Measure.restrict_apply_univ]
    ring
  rw [e2] at h1
  rw [setIntegral_const, Gint_sub hfin hs hst]
  have hnn : 0 ≤ᵐ[P.restrict S] fun ω => (I t ω - I s ω) ^ 2 := Filter.Eventually.of_forall fun ω => sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae hnn
    (((hM2 t).sub (hM2 s)).integrable_sq.aestronglyMeasurable.restrict)]
  have e3 : ∫⁻ ω in S, ENNReal.ofReal ((I t ω - I s ω) ^ 2) ∂P =
      ∫⁻ ω in S, ‖I t ω - I s ω‖ₑ ^ 2 ∂P :=
    lintegral_congr fun ω => (enorm_sq_eq_ofReal _).symm
  rw [e3, h1, ENNReal.toReal_mul]
  simp [Measure.real, smul_eq_mul]

lemma Gint_const {k : ℝ} (hk : 0 ≤ k) (t : ℝ) : Gint (fun _ => k) t = k * max t 0 := by
  unfold Gint
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hk, ENNReal.toReal_ofReal']
  simp [sub_zero]

theorem IsItoC.martingale_mul_sub_const (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hξ' : IsCtbl P ℱ ξ') (hI : IsItoC P ℱ 𝔚 ξ I) (hI' : IsItoC P ℱ 𝔚 ξ' I') {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (h1 : ∀ r ω, HasSum (fun a => ξ r ω a ^ 2) 1) (h2 : ∀ r ω, HasSum (fun a => ξ' r ω a ^ 2) 1)
    (h3 : ∀ r ω, HasSum (fun a => ξ r ω a * ξ' r ω a) c) :
    Martingale (fun t ω => I t ω * I' t ω - c * max t 0) ℱ P := by
  have hp := (hI.add hW hξ hξ' hI')
  have hm := (hI.sub hW hξ hξ' hI')
  have hpC := hξ.add hξ'
  have hmC : IsCtbl P ℱ (fun r ω a => ξ r ω a - ξ' r ω a) := by
    have := hξ.add (hξ'.mul_bdd (w := fun _ _ => (-1 : ℝ)) (isProgressive_const ℱ _) (C := 1)
      (fun _ _ => by simp))
    convert this using 3 with r ω a
    ring
  have hsp : ∀ r ω, HasSum (fun a => (ξ r ω a + ξ' r ω a) ^ 2) (2 + 2 * c) := fun r ω => by
    have := ((h1 r ω).add (h2 r ω)).add ((h3 r ω).mul_left 2)
    convert this using 1
    · funext a; ring
    · ring
  have hsm : ∀ r ω, HasSum (fun a => (ξ r ω a - ξ' r ω a) ^ 2) (2 - 2 * c) := fun r ω => by
    have := ((h1 r ω).add (h2 r ω)).sub ((h3 r ω).mul_left 2)
    convert this using 1
    · funext a; ring
    · ring
  have Mp := hp.martingale_sq_sub hW hpC (g := fun _ => 2 + 2 * c)
    (fun r ω => enorm_tsum_sq_of_hasSum (hsp r ω))
  have Mm := hm.martingale_sq_sub hW hmC (g := fun _ => 2 - 2 * c)
    (fun r ω => enorm_tsum_sq_of_hasSum (hsm r ω))
  have key := (Mp.sub Mm).smul (1 / 4 : ℝ)
  convert key using 1
  funext t ω
  simp only [Gint_const (by linarith : 0 ≤ 2 + 2 * c), Gint_const (by linarith : 0 ≤ 2 - 2 * c),
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

end SqMart
end FragR4

section FragR5
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section Block
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ ξ' : ℝ → Ω → A → ℝ}
  {I I' : ℝ → Ω → ℝ}

lemma isProgressive_block {a a' : ℝ} {c : Ω → ℝ} (hc : Measurable[ℱ a] c) :
    IsProgressive ℱ (fun r ω => c ω * (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) r) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  by_cases hai : a ≤ i
  · have h1 : Measurable fun p : Set.Iic i × Ω => c p.2 :=
      (hc.mono (ℱ.mono hai) le_rfl).comp measurable_snd
    have h2 : Measurable fun p : Set.Iic i × Ω => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) (p.1 : ℝ) :=
      (measurable_const.indicator measurableSet_Ioc).comp (measurable_subtype_coe.comp measurable_fst)
    exact h1.mul h2
  · have : (fun p : Set.Iic i × Ω => c p.2 * (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) (p.1 : ℝ)) =
        fun _ => 0 := by
      funext p
      have : (p.1 : ℝ) ∉ Set.Ioc a a' := fun h => hai (h.1.le.trans p.1.2)
      simp [this]
    show Measurable fun p : Set.Iic i × Ω => c p.2 * (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) (p.1 : ℝ)
    rw [this]
    exact measurable_const

lemma block_eq (c : Ω → ℝ) (a a' : ℝ) (ξ : ℝ → Ω → A → ℝ) (r : ℝ) (ω : Ω) (b : A) :
    c ω * (Set.Ioc a a').indicator (fun _ => ξ r ω b) r =
      (c ω * (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) r) * ξ r ω b := by
  by_cases h : r ∈ Set.Ioc a a' <;> simp [h]

theorem IsCtbl.block (hξ : IsCtbl P ℱ ξ) {a a' : ℝ} {c : Ω → ℝ} (hc : Measurable[ℱ a] c) {C : ℝ}
    (hC : ∀ ω, |c ω| ≤ C) :
    IsCtbl P ℱ (fun r ω b => c ω * (Set.Ioc a a').indicator (fun _ => ξ r ω b) r) := by
  have := hξ.mul_bdd (isProgressive_block (a' := a') hc) (C := |C|) (fun r ω => by
    by_cases h : r ∈ Set.Ioc a a'
    · rw [Set.indicator_of_mem h]
      simpa using (hC ω).trans (le_abs_self C)
    · rw [Set.indicator_of_notMem h]
      simp)
  have e : (fun r ω b => c ω * (Set.Ioc a a').indicator (fun _ => ξ r ω b) r) =
      fun r ω b => (c ω * (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) r) * ξ r ω b := by
    funext r ω b
    exact block_eq c a a' ξ r ω b
  rw [e]
  exact this

theorem IsItoC.block (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hI : IsItoC P ℱ 𝔚 ξ I) {a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a') {c : Ω → ℝ}
    (hc : Measurable[ℱ a] c) {C : ℝ} (hC : ∀ ω, |c ω| ≤ C) :
    IsItoC P ℱ 𝔚 (fun r ω b => c ω * (Set.Ioc a a').indicator (fun _ => ξ r ω b) r)
      (fun t ω => c ω * (I (min t a') ω - I (min t a) ω)) := by
  refine ⟨fun ω => continuous_const.mul (((hI.cont ω).comp (continuous_id.min continuous_const)).sub
      ((hI.cont ω).comp (continuous_id.min continuous_const))), fun t => ?_,
    fun t ht ω => by simp [hI.zero _ ((min_le_left _ _).trans ht), hI.zero _ ((min_le_left _ _).trans ht)],
    fun t ht => ?_⟩
  · by_cases hat : a ≤ t
    · have h1 : Measurable[ℱ t] c := hc.mono (ℱ.mono hat) le_rfl
      have h2 : Measurable[ℱ t] (I (min t a')) :=
        (hI.adapted (min t a')).mono (ℱ.mono (min_le_left _ _)) le_rfl
      have h3 : Measurable[ℱ t] (I (min t a)) :=
        (hI.adapted (min t a)).mono (ℱ.mono (min_le_left _ _)) le_rfl
      exact h1.mul (h2.sub h3)
    · have : (fun ω => c ω * (I (min t a') ω - I (min t a) ω)) = fun _ => 0 := by
        funext ω
        have e1 : min t a' = t := min_eq_left (by linarith [not_le.1 hat])
        have e2 : min t a = t := min_eq_left (not_le.1 hat).le
        rw [e1, e2]; simp
      show Measurable[ℱ t] fun ω => c ω * (I (min t a') ω - I (min t a) ω)
      rw [this]; exact measurable_const
  · set u' := min t a' with hu'
    set u := min t a with hu
    have hu'0 : 0 ≤ u' := le_min ht (ha.trans haa')
    have hu0 : 0 ≤ u := le_min ht ha
    have h1 := hI.approx u' hu'0
    have h2 := hI.approx u hu0
    have hb : Tendsto (fun F : Finset A => ‖C‖ₑ ^ 2 * (2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F u' ω - I u' ω‖ₑ ^ 2 ∂P +
        2 * ∫⁻ ω, ‖ItoF P ℱ 𝔚 ξ F u ω - I u ω‖ₑ ^ 2 ∂P)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul
        ((ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
          (ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))) (Or.inr (by simp : ‖C‖ₑ ^ 2 ≠ ⊤))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => bot_le) fun F => ?_
    have hae := itoIntegral_blockInt (hW F) (hξ.progressiveL2 F) ha haa' hc hC t
    have hF1 := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) F u'
    have hF2 := aemeasurable_ItoF (P := P) (ℱ := ℱ) (𝔚 := 𝔚) (ξ := ξ) F u
    have hD1 : AEMeasurable (fun ω => ItoF P ℱ 𝔚 ξ F u' ω - I u' ω) P :=
      hF1.sub (hI.aemeasurable u')
    have hD2 : AEMeasurable (fun ω => ItoF P ℱ 𝔚 ξ F u ω - I u ω) P :=
      hF2.sub (hI.aemeasurable u)
    calc ∫⁻ ω, ‖ItoF P ℱ 𝔚 (fun r ω b => c ω * (Set.Ioc a a').indicator (fun _ => ξ r ω b) r) F t ω -
            c ω * (I u' ω - I u ω)‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ‖c ω‖ₑ ^ 2 * ‖(ItoF P ℱ 𝔚 ξ F u' ω - I u' ω) + -(ItoF P ℱ 𝔚 ξ F u ω - I u ω)‖ₑ ^ 2 ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          have : ItoF P ℱ 𝔚 (fun r ω b => c ω * (Set.Ioc a a').indicator (fun _ => ξ r ω b) r) F t ω =
              c ω * (ItoF P ℱ 𝔚 ξ F u' ω - ItoF P ℱ 𝔚 ξ F u ω) := hω
          have e : c ω * (ItoF P ℱ 𝔚 ξ F u' ω - ItoF P ℱ 𝔚 ξ F u ω) - c ω * (I u' ω - I u ω) =
              c ω * ((ItoF P ℱ 𝔚 ξ F u' ω - I u' ω) + -(ItoF P ℱ 𝔚 ξ F u ω - I u ω)) := by ring
          rw [this, e, enorm_mul, mul_pow]
      _ ≤ ∫⁻ ω, ‖C‖ₑ ^ 2 * (2 * ‖ItoF P ℱ 𝔚 ξ F u' ω - I u' ω‖ₑ ^ 2 +
            2 * ‖ItoF P ℱ 𝔚 ξ F u ω - I u ω‖ₑ ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hcc : ‖c ω‖ₑ ^ 2 ≤ ‖C‖ₑ ^ 2 := by
            gcongr
            rw [← ofReal_norm, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (by simpa using (hC ω).trans (le_abs_self C))
          have hs := enorm_add_sq_le (ItoF P ℱ 𝔚 ξ F u' ω - I u' ω) (-(ItoF P ℱ 𝔚 ξ F u ω - I u ω))
          rw [enorm_neg] at hs
          exact mul_le_mul' hcc hs
      _ = _ := by
          have hA1 : AEMeasurable (fun ω => 2 * ‖ItoF P ℱ 𝔚 ξ F u' ω - I u' ω‖ₑ ^ 2) P :=
            (hD1.enorm.pow_const 2).const_mul 2
          rw [lintegral_const_mul' _ _ (by simp),
            lintegral_add_left' hA1 (fun ω => 2 * ‖ItoF P ℱ 𝔚 ξ F u ω - I u ω‖ₑ ^ 2),
            lintegral_const_mul'' _ (hD1.enorm.pow_const 2), lintegral_const_mul'' _ (hD2.enorm.pow_const 2)]

end Block
end FragR5

section FragR6
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section ElemInt
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ ξ' : ℝ → Ω → A → ℝ}
  {I I' : ℝ → Ω → ℝ}

lemma isCtbl_zero : IsCtbl P ℱ (fun (_ : ℝ) (_ : Ω) (_ : A) => (0 : ℝ)) := by
  refine ⟨fun a => isProgressive_const ℱ (0 : ℝ), fun T => ?_⟩
  simp [cT]

theorem isItoC_zero (hW : IsCylindricalBrownian P ℱ 𝔚) :
    IsItoC P ℱ 𝔚 (fun (_ : ℝ) (_ : Ω) (_ : A) => (0 : ℝ)) (fun _ _ => 0) := by
  refine ⟨fun ω => continuous_const, fun t => measurable_const, fun t _ ω => rfl, fun t ht => ?_⟩
  have : ∀ F : Finset A, ∫⁻ ω, ‖ItoF P ℱ 𝔚 (fun (_ : ℝ) (_ : Ω) (_ : A) => (0 : ℝ)) F t ω - 0‖ₑ ^ 2 ∂P = 0 := by
    intro F
    simp only [sub_zero]
    have := lintegral_itoIntegral_sq (hW F) ((isCtbl_zero (P := P) (ℱ := ℱ) (A := A)).progressiveL2 F) t
    simp only [ItoF]
    refine (this.trans ?_ : _ = _)
    simp [sqIntegralOn, ξF]
  simp_rw [this]
  exact tendsto_const_nhds

theorem IsItoC.finset_sum (hW : IsCylindricalBrownian P ℱ 𝔚) {γ : Type*} (S : Finset γ)
    (ξs : γ → ℝ → Ω → A → ℝ) (Is : γ → ℝ → Ω → ℝ) (hξ : ∀ c ∈ S, IsCtbl P ℱ (ξs c))
    (hI : ∀ c ∈ S, IsItoC P ℱ 𝔚 (ξs c) (Is c)) :
    IsCtbl P ℱ (fun r ω a => ∑ c ∈ S, ξs c r ω a) ∧
      IsItoC P ℱ 𝔚 (fun r ω a => ∑ c ∈ S, ξs c r ω a) (fun t ω => ∑ c ∈ S, Is c t ω) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨by simpa using isCtbl_zero, by simpa using isItoC_zero hW⟩
  | insert c S hc ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun d hd => hξ d (Finset.mem_insert_of_mem hd))
      (fun d hd => hI d (Finset.mem_insert_of_mem hd))
    have h1 := hξ c (Finset.mem_insert_self c S)
    have h2 := hI c (Finset.mem_insert_self c S)
    have e1 : (fun r ω a => ∑ d ∈ insert c S, ξs d r ω a) =
        fun r ω a => ξs c r ω a + ∑ d ∈ S, ξs d r ω a := by
      funext r ω a; rw [Finset.sum_insert hc]
    have e2 : (fun t ω => ∑ d ∈ insert c S, Is d t ω) =
        fun t ω => Is c t ω + ∑ d ∈ S, Is d t ω := by
      funext t ω; rw [Finset.sum_insert hc]
    rw [e1, e2]
    exact ⟨h1.add ih1, h2.add hW h1 ih1 ih2⟩

lemma IsItoC.coe_toNNReal (hI : IsItoC P ℱ 𝔚 ξ I) (x : ℝ) :
    I ((Real.toNNReal x : ℝ≥0) : ℝ) = I x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [Real.toNNReal_of_nonpos hx]
    simp only [NNReal.coe_zero]
    funext ω
    rw [hI.zero 0 le_rfl ω, hI.zero x hx ω]
  · rw [Real.coe_toNNReal x hx.le]

theorem isItoC_elem (hW : IsCylindricalBrownian P ℱ 𝔚) {J : Type*} [Fintype J]
    (ψ : J → ℝ → Ω → A → ℝ) (Bj : J → ℝ → Ω → ℝ) (hψ : ∀ j, IsCtbl P ℱ (ψ j))
    (hB : ∀ j, IsItoC P ℱ 𝔚 (ψ j) (Bj j)) (Ξ : SimpleIntegrand ℱ J) :
    IsItoC P ℱ 𝔚 (fun r ω a => ∑ j, Ξ.toFun r ω j * ψ j r ω a)
      (Ξ.elemIntegral (fun t ω j => Bj j (t : ℝ) ω)) := by
  obtain ⟨C, hC⟩ := Ξ.bdd
  have ht0 : ∀ i : Fin Ξ.n, 0 ≤ Ξ.t i.castSucc := fun i =>
    Ξ.nonneg.trans (Ξ.mono (Fin.zero_le _))
  have hmono : ∀ i : Fin Ξ.n, Ξ.t i.castSucc ≤ Ξ.t i.succ := fun i =>
    Ξ.mono (Fin.castSucc_le_succ i)
  have key := IsItoC.finset_sum hW (Finset.univ : Finset (Fin Ξ.n × J))
    (fun p r ω a => Ξ.ξ p.1 ω p.2 * (Set.Ioc (Ξ.t p.1.castSucc) (Ξ.t p.1.succ)).indicator
      (fun _ => ψ p.2 r ω a) r)
    (fun p t ω => Ξ.ξ p.1 ω p.2 * (Bj p.2 (min t (Ξ.t p.1.succ)) ω -
      Bj p.2 (min t (Ξ.t p.1.castSucc)) ω))
    (fun p _ => (hψ p.2).block (a := Ξ.t p.1.castSucc) (a' := Ξ.t p.1.succ)
      (c := fun ω => Ξ.ξ p.1 ω p.2) ((measurable_pi_apply p.2).comp (Ξ.meas p.1)) (C := C)
      (fun ω => hC p.1 ω p.2))
    (fun p _ => (hB p.2).block hW (hψ p.2) (ht0 p.1) (hmono p.1)
      ((measurable_pi_apply p.2).comp (Ξ.meas p.1)) (C := C) (fun ω => hC p.1 ω p.2))
  have e1 : (fun r ω a => ∑ j, Ξ.toFun r ω j * ψ j r ω a) =
      fun r ω a => ∑ p ∈ (Finset.univ : Finset (Fin Ξ.n × J)), Ξ.ξ p.1 ω p.2 *
        (Set.Ioc (Ξ.t p.1.castSucc) (Ξ.t p.1.succ)).indicator (fun _ => ψ p.2 r ω a) r := by
    funext r ω a
    simp only [SimpleIntegrand.toFun, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.univ_product_univ.symm, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : r ∈ Set.Ioc (Ξ.t i.castSucc) (Ξ.t i.succ) <;> simp [h]
  have e2 : Ξ.elemIntegral (fun t ω j => Bj j (t : ℝ) ω) =
      fun t ω => ∑ p ∈ (Finset.univ : Finset (Fin Ξ.n × J)), Ξ.ξ p.1 ω p.2 *
        (Bj p.2 (min t (Ξ.t p.1.succ)) ω - Bj p.2 (min t (Ξ.t p.1.castSucc)) ω) := by
    funext t ω
    simp only [SimpleIntegrand.elemIntegral, (hB _).coe_toNNReal, min_comm t]
    rw [Finset.univ_product_univ.symm, Finset.sum_product]
  rw [e1, e2]
  exact key.2

end ElemInt
end FragR6

section FragR7
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section Assoc
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ}
  {J : Type*} [Fintype J] {ψ : J → ℝ → Ω → A → ℝ}

lemma hasSum_comb_sq (d : J → ℝ) (u : J → A → ℝ)
    (hu : ∀ j j', HasSum (fun a => u j a * u j' a) (if j = j' then (1 : ℝ) else 0)) :
    HasSum (fun a => (∑ j, d j * u j a) ^ 2) (∑ j, d j ^ 2) := by
  have h : ∀ j j', HasSum (fun a => d j * d j' * (u j a * u j' a))
      (d j * d j' * (if j = j' then (1 : ℝ) else 0)) := fun j j' => (hu j j').mul_left _
  have h2 : HasSum (fun a => ∑ j, ∑ j', d j * d j' * (u j a * u j' a))
      (∑ j, ∑ j', d j * d j' * (if j = j' then (1 : ℝ) else 0)) :=
    hasSum_sum fun j _ => hasSum_sum fun j' _ => h j j'
  convert h2 using 1
  · funext a
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · simp [sq]
    · intro j' _ hj'; simp [Ne.symm hj']
    · simp

variable (hψ : ∀ j, ∀ a, IsProgressive ℱ (fun r ω => ψ j r ω a))
include hψ

lemma tsum_cT_comb (hortho : ∀ r ω j j', HasSum (fun a => ψ j r ω a * ψ j' r ω a)
      (if j = j' then (1 : ℝ) else 0))
    {d : ℝ → Ω → J → ℝ} (hd : IsProgressive ℱ d) (T : ℝ) :
    ∑' a, cT P (fun r ω a => ∑ j, d r ω j * ψ j r ω a) a T = sqIntegralOn P d T := by
  have hprog : ∀ a, IsProgressive ℱ (fun r ω => ∑ j, d r ω j * ψ j r ω a) := fun a =>
    IsProgressive.finsetSum fun j _ => (isProgressive_coord hd j).mul (hψ j a)
  unfold cT
  have e := tsum_lintegral_set_eq (S := Set.univ) (P := P) (ξ := fun r ω a => ∑ j, d r ω j * ψ j r ω a)
    hprog measurableSet_Icc (fun r hr => hr.2 : Set.Icc 0 T ⊆ Set.Iic T)
  simp only [Measure.restrict_univ] at e
  rw [e]
  unfold sqIntegralOn
  refine lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  rw [enorm_tsum_sq_of_hasSum (hasSum_comb_sq (d r ω) (fun j a => ψ j r ω a) (hortho r ω)),
    ← enorm_sum_sq, Real.enorm_eq_ofReal (Finset.sum_nonneg fun k _ => sq_nonneg _)]

lemma isCtbl_comb (hortho : ∀ r ω j j', HasSum (fun a => ψ j r ω a * ψ j' r ω a)
      (if j = j' then (1 : ℝ) else 0))
    {d : ℝ → Ω → J → ℝ} (hd : IsProgressiveL2 P ℱ d) :
    IsCtbl P ℱ (fun r ω a => ∑ j, d r ω j * ψ j r ω a) :=
  ⟨fun a => IsProgressive.finsetSum fun j _ => (isProgressive_coord hd.prog j).mul (hψ j a),
    fun T => by
      rw [tsum_cT_comb hψ hortho hd.prog T]
      exact (hd.sq T).ne⟩

end Assoc

section Assoc2
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ}
  {J : Type*} [Fintype J] {ψ : J → ℝ → Ω → A → ℝ}

theorem isItoIntegral_assoc (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hψ' : ∀ j, IsCtbl P ℱ (ψ j)) {Bj : J → ℝ → Ω → ℝ} (hB : ∀ j, IsItoC P ℱ 𝔚 (ψ j) (Bj j))
    (hBr : IsBrownianFiltration P ℱ (fun t ω j => Bj j (t : ℝ) ω))
    (hortho : ∀ r ω j j', HasSum (fun a => ψ j r ω a * ψ j' r ω a) (if j = j' then (1 : ℝ) else 0))
    {f : ℝ → Ω → J → ℝ} (hf : IsProgressiveL2 P ℱ f) {Y : ℝ → Ω → ℝ}
    (hY : IsItoC P ℱ 𝔚 (fun r ω a => ∑ j, f r ω j * ψ j r ω a) Y) :
    IsItoIntegral P ℱ (fun t ω j => Bj j (t : ℝ) ω) f Y := by
  have hψp : ∀ j a, IsProgressive ℱ (fun r ω => ψ j r ω a) := fun j a => (hψ' j).prog a
  refine isItoIntegral_of_exists_seq hBr hf hY.cont (fun t => hY.adapted t)
    (fun t ht ω => hY.zero t ht ω) fun t ht => ?_
  obtain ⟨Ξ, hΞ⟩ := exists_simple_approx P ℱ f hf.prog t (hf.sq t)
  refine ⟨Ξ, hΞ, ?_⟩
  have hfC := isCtbl_comb hψp hortho hf
  have hbound : ∀ n, ∫⁻ ω, ‖(Ξ n).elemIntegral (fun t ω j => Bj j (t : ℝ) ω) t ω - Y t ω‖ₑ ^ 2 ∂P ≤
      sqIntegralOn P (fun s ω => (Ξ n).toFun s ω - f s ω) t := by
    intro n
    have hI := isItoC_elem hW ψ Bj hψ' hB (Ξ n)
    have hΞC := isCtbl_comb hψp hortho (IsProgressiveL2.simple P (Ξ n))
    have hd := hI.sub hW hΞC hfC hY
    have hdC : IsProgressiveL2 P ℱ (fun s ω => (Ξ n).toFun s ω - f s ω) :=
      (IsProgressiveL2.simple P (Ξ n)).sub hf
    have hdCt := isCtbl_comb hψp hortho hdC
    have e : (fun r ω a => ∑ j, (Ξ n).toFun r ω j * ψ j r ω a - ∑ j, f r ω j * ψ j r ω a) =
        fun r ω a => ∑ j, ((Ξ n).toFun r ω j - f r ω j) * ψ j r ω a := by
      funext r ω a
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e] at hd
    have := hd.lintegral_sq_le hdCt hW ht
    rw [tsum_cT_comb hψp hortho hdC.prog t] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΞ (fun _ => bot_le) hbound

end Assoc2
end FragR7

section FragR8
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section LevyItoC
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ}
  {J : Type*} [Countable J] {ψ : J → ℝ → Ω → A → ℝ}

theorem isCylindricalBrownian_of_itoC (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hψ : ∀ j, IsCtbl P ℱ (ψ j)) {Bj : J → ℝ → Ω → ℝ} (hB : ∀ j, IsItoC P ℱ 𝔚 (ψ j) (Bj j))
    (hortho : ∀ r ω i j, HasSum (fun a => ψ i r ω a * ψ j r ω a) (if i = j then (1 : ℝ) else 0)) :
    IsCylindricalBrownian P ℱ (fun t ω j => Bj j (t : ℝ) ω) := by
  intro s
  have hcoe : ∀ (j : J) (t : ℝ) (ω : Ω), Bj j ((Real.toNNReal t : ℝ≥0) : ℝ) ω = Bj j t ω :=
    fun j t ω => congrFun ((hB j).coe_toNNReal t) ω
  have hc : ∀ (k : s) (t : ℝ) (ω : Ω),
      ofNNRealTime (fun (t : ℝ≥0) ω (j : s) => Bj j (t : ℝ) ω) t ω k = Bj k t ω :=
    fun k t ω => hcoe k t ω
  refine levy_characterization P ℱ (hW ∅).complete _ ?_ ?_ ?_ ?_ ?_
  · intro t
    refine Measurable.of_comap_le (comap_fun_le _ fun k => ?_)
    exact ((hB k).adapted (t : ℝ)).comap_le
  · intro ω
    funext k
    exact (hB k).zero 0 le_rfl ω
  · intro ω
    exact continuous_pi fun k => (hB k).cont ω |>.comp NNReal.continuous_coe
  · intro k
    have := (hB k).martingale (hψ k) hW
    convert this using 2 with t
    funext ω
    exact hc k t ω
  · intro k l
    have h1 : ∀ r ω, HasSum (fun a => ψ k r ω a ^ 2) 1 := fun r ω => by
      have := hortho r ω k k
      simpa [sq] using this
    have h2 : ∀ r ω, HasSum (fun a => ψ l r ω a ^ 2) 1 := fun r ω => by
      have := hortho r ω l l
      simpa [sq] using this
    have := (hB k).martingale_mul_sub_const hW (hψ k) (hψ l) (hB l)
      (c := if (k : J) = l then 1 else 0) (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
      h1 h2 (fun r ω => hortho r ω k l)
    convert this using 2 with t
    funext ω
    simp only [ofNNRealTime_apply]
    rw [hcoe k.1 t ω, hcoe l.1 t ω]
    by_cases h : (k : J) = l
    · have h' : k = l := Subtype.ext h
      simp [h, h']
    · have h' : ¬ k = l := fun e => h (congrArg Subtype.val e)
      simp [h, h']

end LevyItoC
end FragR8

section FragR9
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section CylCoords
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {κ : Type*} [Countable κ] {W : ℝ≥0 → Ω → κ → ℝ}

lemma IsCylindricalBrownian.zero_coord (hW : IsCylindricalBrownian P ℱ W) (ω : Ω) (k : κ) :
    W 0 ω k = 0 := by
  have := congrFun ((hW {k}).zero ω) ⟨k, by simp⟩
  simpa using this

lemma IsCylindricalBrownian.continuous_coord (hW : IsCylindricalBrownian P ℱ W) (ω : Ω) (k : κ) :
    Continuous fun t => W t ω k :=
  (continuous_apply (⟨k, by simp⟩ : ({k} : Finset κ))).comp ((hW {k}).cont ω)

theorem isCylindricalBrownian_of_coords (hcomplete : IsCompleteFiltration P ℱ)
    (hadapted : ∀ (t : ℝ≥0) (k : κ), Measurable[ℱ t] (fun ω => W t ω k))
    (h0 : ∀ ω k, W 0 ω k = 0) (hcont : ∀ ω k, Continuous fun t => W t ω k)
    (hmart : ∀ k, Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k) ℱ P)
    (hqv : ∀ k l, Martingale (fun (t : ℝ) ω => ofNNRealTime W t ω k * ofNNRealTime W t ω l -
      if k = l then max t 0 else 0) ℱ P) :
    IsCylindricalBrownian P ℱ W := by
  intro s
  refine levy_characterization P ℱ hcomplete _ ?_ ?_ ?_ ?_ ?_
  · intro t
    refine Measurable.of_comap_le (comap_fun_le _ fun k => ?_)
    exact (hadapted t k).comap_le
  · intro ω; funext k; exact h0 ω k
  · intro ω; exact continuous_pi fun k => hcont ω k
  · intro k; exact hmart k
  · intro k l
    have := hqv k l
    convert this using 2 with t
    funext ω
    by_cases h : k = l
    · have h' : (k : κ) = l := congrArg Subtype.val h
      simp [h, h']
    · have h' : ¬ (k : κ) = l := fun e => h (Subtype.ext e)
      simp [h, h']

theorem IsCylindricalBrownian.comp_inj {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A]
    {𝔚 : ℝ≥0 → Ω → A → ℝ} (hW : IsCylindricalBrownian P ℱ 𝔚) {γ : Type*} [Countable γ]
    (X : γ → A) (hX : Function.Injective X) :
    IsCylindricalBrownian P ℱ (fun t ω c => 𝔚 t ω (X c)) := by
  refine isCylindricalBrownian_of_coords (hW ∅).complete (fun t c => hW.measurable_coord t (X c))
    (fun ω c => hW.zero_coord ω (X c)) (fun ω c => hW.continuous_coord ω (X c))
    (fun c => hW.martingale_coord (X c)) (fun c d => ?_)
  have := hW.martingale_mul_sub (X c) (X d)
  by_cases h : c = d
  · subst h; simpa using this
  · have h' : ¬ X c = X d := fun e => h (hX e)
    simpa [h, h'] using this

end CylCoords
end FragR9

section FragR10
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section Trans
open Classical
variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {ℱ : Filtration ℝ mΩ}
  {ℱ' : Filtration ℝ mΩ'} {π : Ω' → Ω} {s : Type*} [Fintype s]

/-- Pull-back of a simple integrand along a map that is measurable for the filtrations. -/
def SimpleIntegrand.comapπ (π : Ω' → Ω) (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) (Ψ : SimpleIntegrand ℱ s) :
    SimpleIntegrand ℱ' s where
  n := Ψ.n
  t := Ψ.t
  mono := Ψ.mono
  nonneg := Ψ.nonneg
  ξ := fun i ω' => Ψ.ξ i (π ω')
  meas := fun i => (Ψ.meas i).comp (hπ _)
  bdd := by obtain ⟨C, hC⟩ := Ψ.bdd; exact ⟨C, fun i ω k => hC i (π ω) k⟩

lemma SimpleIntegrand.comapπ_toFun (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) (Ψ : SimpleIntegrand ℱ s)
    (r : ℝ) (ω' : Ω') : (Ψ.comapπ π hπ).toFun r ω' = Ψ.toFun r (π ω') := rfl

lemma SimpleIntegrand.comapπ_elem (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) (Ψ : SimpleIntegrand ℱ s)
    (W : ℝ≥0 → Ω → s → ℝ) (r : ℝ) (ω' : Ω') :
    (Ψ.comapπ π hπ).elemIntegral (fun t ω' k => W t (π ω') k) r ω' = Ψ.elemIntegral W r (π ω') := rfl

lemma isProgressive_comp_π (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) {β : Type*} [MeasurableSpace β]
    {g : ℝ → Ω → β} (hg : IsProgressive ℱ g) : IsProgressive ℱ' (fun r ω' => g r (π ω')) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω') := Subtype.instMeasurableSpace.prod (ℱ' i)
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have h1 : Measurable (fun p : Set.Iic i × Ω' => (p.1, π p.2)) :=
    measurable_fst.prodMk ((hπ i).comp measurable_snd)
  exact (hg i).comp h1

lemma sqIntegralOn_comp_π (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) (hπp : MeasurePreserving π P' P)
    {g : ℝ → Ω → s → ℝ} (hg : IsProgressive ℱ g) (T : ℝ) :
    sqIntegralOn P' (fun r ω' => g r (π ω')) T = sqIntegralOn P g T := by
  rw [sqIntegralOn_eq_clamp, sqIntegralOn_eq_clamp]
  have hm := measurable_lintegral_sqSum hg T
  exact hπp.lintegral_comp hm

theorem itoIntegral_comp_π (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) (hπp : MeasurePreserving π P' P)
    {W : ℝ≥0 → Ω → s → ℝ} (hW : IsBrownianFiltration P ℱ W)
    (hW' : IsBrownianFiltration P' ℱ' (fun t ω' k => W t (π ω') k))
    {g : ℝ → Ω → s → ℝ} (hg : IsProgressiveL2 P ℱ g) :
    ∀ᵐ ω' ∂P', ∀ t, itoIntegral P' ℱ' (fun t ω' k => W t (π ω') k) (fun r ω' k => g r (π ω') k) t ω' =
      itoIntegral P ℱ W g t (π ω') := by
  have hg' : IsProgressiveL2 P' ℱ' (fun r ω' k => g r (π ω') k) :=
    ⟨isProgressive_comp_π hπ hg.prog, fun T => by
      rw [sqIntegralOn_comp_π hπ hπp hg.prog T]; exact hg.sq T⟩
  have hI := isItoIntegral_itoIntegral hW hg
  have hM' : IsItoIntegral P' ℱ' (fun t ω' k => W t (π ω') k) (fun r ω' k => g r (π ω') k)
      (fun t ω' => itoIntegral P ℱ W g t (π ω')) := by
    refine isItoIntegral_of_exists_seq hW' hg' (fun ω' => hI.cont (π ω'))
      (fun t => (hI.adapted t).comp (hπ t)) (fun t ht ω' => hI.zero t ht (π ω')) fun t ht => ?_
    obtain ⟨Ψ, hΨ⟩ := exists_simple_approx P ℱ g hg.prog t (hg.sq t)
    refine ⟨fun n => (Ψ n).comapπ π hπ, ?_, ?_⟩
    · unfold IsApprox
      have : ∀ n, sqIntegralOn P' (fun r ω' => (Ψ n).toFun r (π ω') - g r (π ω')) t =
          sqIntegralOn P (fun r ω => (Ψ n).toFun r ω - g r ω) t := fun n =>
        sqIntegralOn_comp_π hπ hπp (g := fun r ω => (Ψ n).toFun r ω - g r ω)
          (isProgressive_sub (Ψ n).isProgressive_toFun hg.prog) t
      simpa only [SimpleIntegrand.comapπ_toFun, this] using hΨ
    · have h1 := hI.approx t ht Ψ hΨ
      have : ∀ n, ∫⁻ ω', ‖((Ψ n).comapπ π hπ).elemIntegral (fun t ω' k => W t (π ω') k) t ω' -
          itoIntegral P ℱ W g t (π ω')‖ₑ ^ 2 ∂P' =
          ∫⁻ ω, ‖(Ψ n).elemIntegral W t ω - itoIntegral P ℱ W g t ω‖ₑ ^ 2 ∂P := fun n => by
        have hm : Measurable fun ω => ‖(Ψ n).elemIntegral W t ω - itoIntegral P ℱ W g t ω‖ₑ ^ 2 :=
          ((((SimpleIntegrand.adapted_elemIntegral hW (Ψ n) t).mono (ℱ.le t) le_rfl).sub
            ((adapted_itoIntegral P ℱ W g t).mono (ℱ.le t) le_rfl)).enorm).pow_const 2
        exact hπp.lintegral_comp hm
      simpa only [this] using h1
  exact (hM'.ae_eq_forall hW' (isItoIntegral_itoIntegral hW' hg') hg').mono fun ω' h t => (h t).symm

end Trans
end FragR10

section FragR11
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section PathIndep
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {γ : Type*} [Fintype γ] {β : ℝ≥0 → Ω → γ → ℝ}

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by `β_τ`, `τ ∈ T`. -/
def pathSigmaFin (β : ℝ≥0 → Ω → γ → ℝ) (T : Finset ℝ≥0) : MeasurableSpace Ω :=
  ⨆ τ ∈ T, MeasurableSpace.comap (β τ) inferInstance

lemma pathSigmaFin_mono {T T' : Finset ℝ≥0} (h : T ⊆ T') : pathSigmaFin β T ≤ pathSigmaFin β T' :=
  iSup₂_le fun r hr => le_iSup₂_of_le (f := fun r (_ : r ∈ T') =>
    MeasurableSpace.comap (β r) inferInstance) r (h hr) le_rfl

theorem indep_zero_pathSigmaFin (hβ : IsBrownianFiltration P ℱ β) (T : Finset ℝ≥0) :
    Indep (ℱ 0) (pathSigmaFin β T) P := by
  induction T using Finset.induction_on_max with
  | empty =>
    have : pathSigmaFin β ∅ = ⊥ := by simp [pathSigmaFin]
    rw [this]
    exact indep_bot_right _
  | insert a s ha ih =>
    have hβm : ∀ τ : ℝ≥0, MeasurableSpace.comap (β τ) inferInstance ≤ ℱ (τ : ℝ) := fun τ =>
      (hβ.adapted τ).comap_le
    rcases s.eq_empty_or_nonempty with rfl | hs
    · -- single time
      have h1 := hβ.indep_incr 0 a (by positivity)
      have e : (fun ω => β a ω - β 0 ω) = β a := by funext ω; simp [hβ.zero]
      rw [e] at h1
      have : pathSigmaFin β (insert a ∅) = MeasurableSpace.comap (β a) inferInstance := by
        simp [pathSigmaFin]
      rw [this]
      exact h1.symm
    · set m := s.max' hs with hm
      have hmle : ∀ r ∈ s, r ≤ m := fun r hr => s.le_max' r hr
      have hma : m ≤ a := (ha m (s.max'_mem hs)).le
      have hCle : pathSigmaFin β s ≤ ℱ (m : ℝ) :=
        iSup₂_le fun r hr => (hβm r).trans (ℱ.mono (by exact_mod_cast hmle r hr))
      have hmeas : MeasurableSpace.comap (fun ω => β a ω - β m ω) inferInstance ≤ mΩ :=
        Measurable.comap_le ((hβ.measurable a).sub (hβ.measurable m))
      have hD : Indep (MeasurableSpace.comap (fun ω => β a ω - β m ω) inferInstance)
          (ℱ 0 ⊔ pathSigmaFin β s) P :=
        indep_of_indep_of_le_right (hβ.indep_incr m a hma)
          (sup_le (ℱ.mono (by exact_mod_cast m.2)) hCle)
      have h3 := indep_sup_right_of_indep (M0 := MeasurableSpace.comap (fun ω => β a ω - β m ω) inferInstance)
        (M1 := ℱ 0) (M2 := pathSigmaFin β s) P hmeas (ℱ.le 0) (iSup₂_le fun r hr => (hβm r).trans (ℱ.le _))
        ih hD
      refine indep_of_indep_of_le_right h3 ?_
      -- pathSigmaFin (insert a s) ≤ D ⊔ C
      unfold pathSigmaFin
      refine iSup₂_le fun r hr => ?_
      rcases Finset.mem_insert.1 hr with rfl | hr'
      · have hd : Measurable[MeasurableSpace.comap (fun ω => β r ω - β m ω) inferInstance ⊔ pathSigmaFin β s]
            (fun ω => β r ω - β m ω) :=
          (comap_measurable (fun ω => β r ω - β m ω)).mono le_sup_left le_rfl
        have hm' : Measurable[MeasurableSpace.comap (fun ω => β r ω - β m ω) inferInstance ⊔ pathSigmaFin β s]
            (β m) :=
          (comap_measurable (β m)).mono (le_sup_of_le_right (le_iSup₂_of_le (f := fun τ (_ : τ ∈ s) =>
            MeasurableSpace.comap (β τ) inferInstance) m (s.max'_mem hs) le_rfl)) le_rfl
        have h1 := hd.add hm'
        have e : ((fun ω => β r ω - β m ω) + β m) = β r := by funext ω; simp
        rw [e] at h1
        exact h1.comap_le
      · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun τ (_ : τ ∈ s) =>
          MeasurableSpace.comap (β τ) inferInstance) r hr' le_rfl)

end PathIndep

section PathIndep2
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {J : Type*} [Countable J] {B : ℝ≥0 → Ω → J → ℝ}

lemma comap_coord_le_comap_pi {Ξ : Type*} {s : Type*} (g : Ξ → s → ℝ) (k : s) :
    MeasurableSpace.comap (fun ω => g ω k) inferInstance ≤ MeasurableSpace.comap g inferInstance := by
  rw [show (fun ω => g ω k) = (fun v : s → ℝ => v k) ∘ g from rfl, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply k).comap_le

theorem indep_zero_cylPath (hB : IsCylindricalBrownian P ℱ B) :
    Indep (ℱ 0) (⨆ (τ : ℝ≥0) (k : J), MeasurableSpace.comap (fun ω => B τ ω k) inferInstance) P := by
  -- finite coordinate sets
  set N : Finset J → MeasurableSpace Ω := fun s =>
    ⨆ T : Finset ℝ≥0, pathSigmaFin (fun t ω (k : s) => B t ω k) T with hN
  have hNle : ∀ s, N s ≤ mΩ := fun s =>
    iSup_le fun T => iSup₂_le fun τ _ => ((hB s).measurable τ).comap_le
  have hNi : ∀ s, Indep (N s) (ℱ 0) P := fun s => by
    refine indep_iSup_of_directed_le (fun T => (indep_zero_pathSigmaFin (hB s) T).symm)
      (fun T => iSup₂_le fun τ _ => ((hB s).measurable τ).comap_le) (ℱ.le 0) ?_
    intro T T'
    exact ⟨T ∪ T', pathSigmaFin_mono Finset.subset_union_left, pathSigmaFin_mono Finset.subset_union_right⟩
  have hNmono : Monotone N := by
    intro s s' hss'
    refine iSup_le fun T => ?_
    -- coordinates of s are coordinates of s'
    refine iSup₂_le fun τ hτ => ?_
    refine le_trans ?_ (le_iSup_of_le T (le_iSup₂_of_le τ hτ le_rfl))
    refine comap_fun_le _ fun k => ?_
    exact comap_coord_le_comap_pi (fun ω (j : s') => B τ ω j) ⟨k, hss' k.2⟩
  have hbig : Indep (⨆ s : Finset J, N s) (ℱ 0) P :=
    indep_iSup_of_directed_le hNi hNle (ℱ.le 0) (hNmono.directed_le)
  refine (indep_of_indep_of_le_left hbig ?_).symm
  refine iSup₂_le fun τ k => ?_
  refine le_trans ?_ (le_iSup N {k})
  refine le_trans ?_ (le_iSup_of_le {τ} (le_iSup₂_of_le τ (by simp) le_rfl))
  exact comap_coord_le_comap_pi (fun ω (j : ({k} : Finset J)) => B τ ω j) ⟨k, by simp⟩

end PathIndep2
end FragR11

section FragR12
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators
section PolarFam
open Classical
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ] {ι : Type*} [Countable ι]

/-- Properties of a coordinate map into `ℓ²`: linear isometry coordinatewise. -/
structure CoordProps (c : H → κ ⊕ ι → ℝ) : Prop where
  sq : ∀ x, HasSum (fun a => c x a ^ 2) (‖x‖ ^ 2)
  add : ∀ x y a, c (x + y) a = c x a + c y a
  smul : ∀ (r : ℝ) x a, c (r • x) a = r * c x a

lemma CoordProps.sub {c : H → κ ⊕ ι → ℝ} (hc : CoordProps c) (x y : H) (a : κ ⊕ ι) :
    c (x - y) a = c x a - c y a := by
  have h := hc.add (x - y) y a
  rw [sub_add_cancel] at h
  linarith

lemma CoordProps.sum {c : H → κ ⊕ ι → ℝ} (hc : CoordProps c) {γ : Type*} (s : Finset γ) (v : γ → H)
    (a : κ ⊕ ι) : c (∑ j ∈ s, v j) a = ∑ j ∈ s, c (v j) a := by
  induction s using Finset.induction_on with
  | empty =>
    have := hc.smul 0 0 a
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hc.add, ih]

lemma CoordProps.abs_le {c : H → κ ⊕ ι → ℝ} (hc : CoordProps c) (x : H) (a : κ ⊕ ι) :
    |c x a| ≤ ‖x‖ := by
  have h1 : c x a ^ 2 ≤ ‖x‖ ^ 2 := by
    have := le_hasSum (hc.sq x) a (fun b _ => sq_nonneg _)
    exact this
  exact abs_le_of_sq_le_sq' h1 (norm_nonneg _) |> fun h => _root_.abs_le.2 h

lemma CoordProps.hasSum_mul {c : H → κ ⊕ ι → ℝ} (hc : CoordProps c) (x y : H) :
    HasSum (fun a => c x a * c y a) (inner ℝ x y) := by
  have h1 := hc.sq (x + y)
  have h2 := hc.sq (x - y)
  have h3 := (h1.sub h2).mul_left (1 / 4 : ℝ)
  convert h3 using 1
  · funext a
    rw [hc.add, hc.sub]; ring
  · have := re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (𝕜 := ℝ) x y
    simp only [RCLike.re_to_real] at this
    rw [this]
    ring

/-- The coordinate functional as a continuous linear map. -/
def CoordProps.toCLM {c : H → κ ⊕ ι → ℝ} (hc : CoordProps c) (a : κ ⊕ ι) : H →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => c v a
      map_add' := fun x y => hc.add x y a
      map_smul' := fun r x => by simpa using hc.smul r x a } 1 (fun v => by
    simpa using hc.abs_le v a)

lemma CoordProps.toCLM_apply {c : H → κ ⊕ ι → ℝ} (hc : CoordProps c) (a : κ ⊕ ι) (v : H) :
    hc.toCLM a v = c v a := rfl

/-- The space of square-summable families. -/
abbrev SumFam (κ H : Type*) [NormedAddCommGroup H] := {z : κ → H // Summable fun k => ‖z k‖ ^ 2}

theorem exists_polar_family {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    (e : HilbertBasis ι ℝ H) (Φ : ℝ → Ω → κ → H)
    (hΦp : ∀ k, IsProgressive ℱ (fun r ω => Φ r ω k))
    (hΦs : ∀ r ω, Summable fun k => ‖Φ r ω k‖ ^ 2) :
    ∃ (S : ℝ → Ω → H →L[ℝ] H) (ψ : ι → ℝ → Ω → κ ⊕ ι → ℝ),
      (∀ r ω, IsSqrtOfForm (S r ω) (hsCovForm (Φ r ω))) ∧
      (∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)) ∧
      (∀ j a, IsProgressive ℱ (fun r ω => ψ j r ω a)) ∧
      (∀ r ω i j, HasSum (fun a => ψ i r ω a * ψ j r ω a) (if i = j then (1 : ℝ) else 0)) ∧
      (∀ x r ω a, HasSum (fun j => inner ℝ (S r ω (e j)) x * ψ j r ω a)
        (Sum.elim (fun k => inner ℝ (Φ r ω k) x) (fun _ => (0 : ℝ)) a)) ∧
      (∀ x r ω, HasSum (fun j => inner ℝ (S r ω (e j)) x ^ 2) (‖S r ω x‖ ^ 2)) ∧
      (∀ (s : Finset ι) x r ω, HasSum (fun a => (Sum.elim (fun k => inner ℝ (Φ r ω k) x)
          (fun _ => (0 : ℝ)) a - ∑ j ∈ s, inner ℝ (S r ω (e j)) x * ψ j r ω a) ^ 2)
        (∑' j, if j ∈ s then 0 else inner ℝ (S r ω (e j)) x ^ 2)) := by
  obtain ⟨S₀, coord, hSm, hSq, hcm, hcsq, hcadd, hcsmul, hcl, hcr⟩ :=
    exists_polar_coords (Z := SumFam κ H) e (fun z k => z.1 k)
      (fun k => (measurable_pi_apply k).comp measurable_subtype_coe) (fun z => z.2)
  have hc : ∀ z, CoordProps (coord z) := fun z => ⟨hcsq z, hcadd z, hcsmul z⟩
  set Φ' : ℝ → Ω → SumFam κ H := fun r ω => ⟨Φ r ω, hΦs r ω⟩ with hΦ'
  have hΦ'p : IsProgressive ℱ Φ' := fun i => by
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact Measurable.subtype_mk (measurable_pi_iff.2 fun k => hΦp k i)
  have hSsymm : ∀ z x y, inner ℝ (S₀ z x) y = inner ℝ x (S₀ z y) := fun z x y => (hSq z).symm x y
  refine ⟨fun r ω => S₀ (Φ' r ω), fun j r ω a => coord (Φ' r ω) (e j) a, fun r ω => hSq _,
    fun x y i => by
      letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
      exact ((hSm x).comp (hΦ'p i)).inner measurable_const,
    fun j a i => by
      letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
      exact (hcm (e j) a).comp (hΦ'p i), ?_, ?_, ?_, ?_⟩
  · intro r ω i j
    have := (hc (Φ' r ω)).hasSum_mul (e i) (e j)
    rwa [orthonormal_iff_ite.1 e.orthonormal i j] at this
  · intro x r ω a
    set z := Φ' r ω with hz
    have h1 := ((e.hasSum_repr (S₀ z x)).mapL ((hc z).toCLM a))
    have h2 : (hc z).toCLM a (S₀ z x) = Sum.elim (fun k => inner ℝ (Φ r ω k) x) (fun _ => (0 : ℝ)) a := by
      rw [CoordProps.toCLM_apply]
      rcases a with k | l
      · exact hcl z x k
      · exact hcr z x l
    rw [h2] at h1
    convert h1 using 1
    funext j
    rw [map_smul, CoordProps.toCLM_apply, smul_eq_mul, HilbertBasis.repr_apply_apply,
      ← hSsymm z (e j) x, real_inner_comm]
  · intro x r ω
    have := e.hasSum_inner_mul_inner (S₀ (Φ' r ω) x) (S₀ (Φ' r ω) x)
    rw [real_inner_self_eq_norm_sq] at this
    convert this using 1
    funext j
    show inner ℝ (S₀ (Φ' r ω) (e j)) x ^ 2 = _
    rw [hSsymm _ (e j) x, sq, real_inner_comm (S₀ (Φ' r ω) x) (e j)]
  · intro s x r ω
    set z := Φ' r ω with hz
    set v : H := S₀ z x - ∑ j ∈ s, inner ℝ (S₀ z (e j)) x • e j with hv
    have hcv : ∀ a, coord z v a = Sum.elim (fun k => inner ℝ (Φ r ω k) x) (fun _ => (0 : ℝ)) a -
        ∑ j ∈ s, inner ℝ (S₀ z (e j)) x * coord z (e j) a := by
      intro a
      rw [hv, (hc z).sub, (hc z).sum]
      have h2 : coord z (S₀ z x) a = Sum.elim (fun k => inner ℝ (Φ r ω k) x) (fun _ => (0 : ℝ)) a := by
        rcases a with k | l
        · exact hcl z x k
        · exact hcr z x l
      rw [h2]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hcsmul]
    have h1 := (hc z).sq v
    have h2 := e.hasSum_inner_mul_inner v v
    rw [real_inner_self_eq_norm_sq] at h2
    have h3 : ∀ j, inner ℝ v (e j) = if j ∈ s then 0 else inner ℝ (S₀ z (e j)) x := by
      intro j
      rw [hv, inner_sub_left, sum_inner]
      simp only [inner_smul_left, conj_trivial]
      have : ∀ j', inner ℝ (e j') (e j) = if j' = j then (1 : ℝ) else 0 := fun j' =>
        orthonormal_iff_ite.1 e.orthonormal j' j
      simp only [this]
      have hj' : inner ℝ (S₀ z (e j)) x = inner ℝ (S₀ z x) (e j) := by
        rw [hSsymm z (e j) x, real_inner_comm]
      by_cases hj : j ∈ s <;> simp [hj, mul_ite, Finset.sum_ite_eq', ← hj']
    have h4 : HasSum (fun j => (if j ∈ s then 0 else inner ℝ (S₀ z (e j)) x ^ 2))
        (‖v‖ ^ 2) := by
      convert h2 using 1
      funext j
      rw [h3 j, real_inner_comm v (e j), h3 j]
      by_cases hj : j ∈ s <;> simp [hj, sq]
    rw [h4.tsum_eq]
    convert h1 using 1
    funext a
    simp only []
    rw [hcv a]

end PolarFam
end FragR12



/-! ### Auxiliary development for Corollary A.23, part 2 (CLT-02c attempt 5)

The `H`-valued continuous Ito integral `G` of a deterministic integrand against the cylindrical
Brownian motion `B` (`pc_hvalued`, Doob coordinatewise, `PCDetData`, `pc_exists_G`), its
Gaussianity and independence of `ℱ 0` (`pc_law_cond` through `dds_coupling_strong` under the
conditional measures `P(· | A)`, `pc_G_gaussian`), the transfer of `hM` to the integral against `B`
(`pc_Z_isItoC`, `pc_bridge`, through `itoIntegral_pad`, `itoIntegral_comp_π` and associativity), the
`L²` bound (`pc_L2_bound`, `powers_stormer`) and the identification of the discrepancy integral
(`pc_lintegral_covDisc`). -/

section A23Hilb
open HilbertCLTAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

omit [MeasurableSpace H] [BorelSpace H] in
/-- A Hilbert basis of `H` indexed by a countable type in an arbitrary universe. -/
lemma exists_hilbertBasis_ulift.{u} :
    ∃ (ι : Type u) (_ : Countable ι) (_ : HilbertBasis ι ℝ H), True := by
  obtain ⟨ι₀, hc, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  have := hc
  have hv : Orthonormal ℝ (fun j : ULift.{u} ι₀ => (b j.down : H)) :=
    b.orthonormal.comp _ ULift.down_injective
  refine ⟨ULift.{u} ι₀, inferInstance, HilbertBasis.mkOfOrthogonalEqBot hv ?_, trivial⟩
  have hrange : Set.range (fun j : ULift.{u} ι₀ => (b j.down : H)) = Set.range (fun i : ι₀ => (b i : H)) := by
    ext x; constructor
    · rintro ⟨j, rfl⟩; exact ⟨j.down, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩
  rw [hrange, ← Submodule.orthogonal_closure, b.dense_span]
  exact Submodule.top_orthogonal_eq_bot

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
lemma hasSum_diag_decomp {κ ι : Type*} {ℓ : κ → H} (hs : Summable fun j => ‖ℓ j‖ ^ 2)
    (e : HilbertBasis ι ℝ H) :
    HasSum (fun i => ∑' j, inner ℝ (ℓ j) (e i) ^ 2) (∑' j, ‖ℓ j‖ ^ 2) := by
  have hrow : ∀ j, HasSum (fun i => inner ℝ (ℓ j) (e i) ^ 2) (‖ℓ j‖ ^ 2) := fun j => by
    have := e.hasSum_inner_mul_inner (ℓ j) (ℓ j)
    rw [real_inner_self_eq_norm_sq] at this
    have h2 : (fun i => inner ℝ (ℓ j) (e i) ^ 2) =
        fun i => inner ℝ (ℓ j) (e i) * inner ℝ (e i) (ℓ j) := by
      funext i; rw [sq, real_inner_comm (e i) (ℓ j)]
    rw [h2]; exact this
  have hsum : Summable (fun p : κ × ι => inner ℝ (ℓ p.1) (e p.2) ^ 2) := by
    rw [summable_prod_of_nonneg (fun p => sq_nonneg _)]
    exact ⟨fun j => (hrow j).summable, by simpa [(hrow _).tsum_eq] using hs⟩
  set f : ι × κ → ℝ := fun p => inner ℝ (ℓ p.2) (e p.1) ^ 2 with hf
  have hsw : Summable f := by
    have := hsum.comp_injective (Equiv.prodComm ι κ).injective
    exact this
  have h1 : HasSum (fun i => ∑' j, f (i, j)) (∑' p, f p) :=
    hsw.hasSum.prod_fiberwise (fun i => (hsw.prod_factor i).hasSum)
  have h2 : ∑' p, f p = ∑' j, ‖ℓ j‖ ^ 2 := by
    have : ∑' p, f p = ∑' p : κ × ι, inner ℝ (ℓ p.1) (e p.2) ^ 2 :=
      (Equiv.prodComm ι κ).tsum_eq (fun p : κ × ι => inner ℝ (ℓ p.1) (e p.2) ^ 2)
    rw [this, hsum.tsum_prod' (fun j => (hrow j).summable)]
    exact tsum_congr fun j => (hrow j).tsum_eq
  rw [← h2]
  exact h1

lemma IsTraceClassCov.hasSum_basis {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {ι : Type*}
    (e : HilbertBasis ι ℝ H) :
    ∃ T : ℝ, HasSum (fun i => C (e i) (e i)) T ∧ ∀ x, C x x ≤ T * ‖x‖ ^ 2 := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  have hd : ∀ x, C x x = ∑' j, inner ℝ (ℓ j) x ^ 2 := fun x => by
    rw [← (hℓ x x).tsum_eq]; exact tsum_congr fun j => (sq _).symm
  refine ⟨∑' j, ‖ℓ j‖ ^ 2, ?_, fun x => ?_⟩
  · have := hasSum_diag_decomp hs e
    convert this using 2 with i
    exact hd (e i)
  · rw [hd x, ← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun j => ?_) ?_ (hs.mul_right _)
    · rw [← mul_pow, ← sq_abs (inner ℝ (ℓ j) x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    · exact (hℓ x x).summable.congr fun j => (sq _).symm

lemma isTraceClassCov_hsCovForm {κ : Type*} [Countable κ] {Φ : κ → H}
    (hΦ : Summable fun k => ‖Φ k‖ ^ 2) : IsTraceClassCov (hsCovForm Φ) := by
  refine ⟨hsCovForm_symm' hΦ, hsCovForm_nonneg' hΦ, ?_⟩
  obtain ⟨ι, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  refine ⟨ι, b, ?_⟩
  refine (hasSum_diag_decomp hΦ b).summable.congr fun i => ?_
  rw [hsCovForm_apply hΦ]
  exact tsum_congr fun k => (sq _)

lemma exists_sqrt_density {ι : Type*} [Countable ι] (e : HilbertBasis ι ℝ H) (t : ℝ)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    ∃ Sb : ℝ → H →L[ℝ] H, OpMeas Sb ∧ (∀ r ∉ Set.Icc 0 t, Sb r = 0) ∧
      ∀ r ∈ Set.Icc 0 t, IsSqrtOfForm (Sb r) (sb r) := by
  classical
  set A : ℝ → H →L[ℝ] H := fun r => if r ∈ Set.Icc 0 t then formOp (sb r) else 0 with hA
  have hAp : ∀ r, IsPSDOp (A r) := by
    intro r
    by_cases hr : r ∈ Set.Icc 0 t
    · simp only [hA, hr, ite_true]
      exact ⟨fun x y => by
        rw [inner_formOp, real_inner_comm, inner_formOp, (hsb.traceClass r hr).symm],
        fun x => by rw [inner_formOp]; exact (hsb.traceClass r hr).nonneg x⟩
    · simp only [hA, hr, ite_false]
      exact ⟨fun x y => by simp, fun x => by simp⟩
  have hAm : OpMeas A := by
    intro x
    refine measurable_of_inner_basis e (fun i => ?_)
    have : (fun r => inner ℝ (e i) (A r x)) =
        fun r => (Set.Icc 0 t).indicator (fun r => sb r x (e i)) r := by
      funext r
      by_cases hr : r ∈ Set.Icc 0 t
      · simp only [hA, hr, ite_true, Set.indicator_of_mem]
        rw [real_inner_comm, inner_formOp]
      · have h0 : A r = 0 := by simp only [hA, hr, ite_false]
        rw [h0, Set.indicator_of_notMem hr]
        simp
    rw [this]
    exact (hsb.meas x (e i)).indicator measurableSet_Icc
  set c : ℝ → ℝ := fun r => 1 + (Set.Icc 0 t).indicator (fun r => ∑' i, sb r (e i) (e i)) r with hc
  have hcm : Measurable c :=
    measurable_const.add ((Measurable.tsum fun i => hsb.meas (e i) (e i)).indicator measurableSet_Icc)
  have hcpos : ∀ r, 0 < c r := by
    intro r
    by_cases hr : r ∈ Set.Icc 0 t
    · have : 0 ≤ ∑' i, sb r (e i) (e i) := tsum_nonneg fun i => (hsb.traceClass r hr).nonneg _
      simp only [hc, hr, Set.indicator_of_mem]
      linarith
    · simp [hc, hr]
  have hAc : ∀ r x, inner ℝ (A r x) x ≤ c r * ‖x‖ ^ 2 := by
    intro r x
    by_cases hr : r ∈ Set.Icc 0 t
    · obtain ⟨T, hT, hb⟩ := (hsb.traceClass r hr).hasSum_basis e
      simp only [hA, hr, ite_true, inner_formOp, hc, Set.indicator_of_mem, hT.tsum_eq]
      have := hb x
      nlinarith [sq_nonneg ‖x‖]
    · simp only [hA, hr, ite_false]
      simp only [zero_apply, inner_zero_left]
      have := hcpos r
      positivity
  set S0 : ℝ → H →L[ℝ] H := fun r => sqrtOp (c r) (A r) with hS0
  have hS0m : OpMeas S0 := OpMeas.sqrtOp hAm hcm hAp hcpos hAc
  refine ⟨fun r => if r ∈ Set.Icc 0 t then S0 r else 0, ?_, fun r hr => by simp [hr], fun r hr => ?_⟩
  · intro x
    have : (fun r => (if r ∈ Set.Icc 0 t then S0 r else 0) x) =
        (Set.Icc 0 t).indicator (fun r => S0 r x) := by
      funext r
      by_cases hr : r ∈ Set.Icc 0 t <;> simp [hr]
    rw [this]
    exact (hS0m x).indicator measurableSet_Icc
  simp only [hr, ite_true]
  have hspec := sqrtOp_spec (hAp r) (hcpos r) (hAc r)
  refine ⟨hspec.1.symm, hspec.1.nonneg, fun x y => ?_⟩
  rw [hspec.1.symm x (sqrtOp (c r) (A r) y)]
  have : sqrtOp (c r) (A r) (sqrtOp (c r) (A r) y) = A r y := by
    have := congrArg (fun T : H →L[ℝ] H => T y) hspec.2
    simpa using this
  rw [this]
  simp only [hA, hr, ite_true]
  rw [real_inner_comm, inner_formOp, (hsb.traceClass r hr).symm]

lemma IsTraceClassCov.tsum_basis_le {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C) {ι : Type*}
    (e : HilbertBasis ι ℝ H) : ∑' i, C (e i) (e i) ≤ traceNormForm C := by
  classical
  obtain ⟨T, hT, -⟩ := hC.hasSum_basis e
  rw [hT.tsum_eq]
  refine hasSum_le_of_sum_le hT (fun F => ?_)
  have := signed_sum_le_traceNormForm (Z := C) (bddAbove_pairSum hC) (fun i : F => e i)
    (e.orthonormal.comp _ Subtype.val_injective) (fun _ => 1) (fun _ => Or.inl rfl)
  have h2 : ∑ i : F, (1 : ℝ) * C (e i) (e i) = ∑ i ∈ F, C (e i) (e i) := by
    simp only [one_mul]
    exact Finset.sum_coe_sort F (fun i => C (e i) (e i))
  rw [h2] at this
  exact this

end A23Hilb

section PC2
open Classical
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {ξ : ℝ → Ω → A → ℝ}

lemma pc_isProgressive_det {β : Type*} [MeasurableSpace β] {g : ℝ → β} (hg : Measurable g) :
    IsProgressive ℱ (fun r (_ : Ω) => g r) := fun i =>
  (hg.comp measurable_subtype_coe).comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ i))

lemma pc_tsum_cT (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (T : ℝ) :
    ∑' a, cT P ξ a T = ∫⁻ ω, (∫⁻ r in Set.Icc 0 T, ∑' a, ‖ξ r ω a‖ₑ ^ 2) ∂P := by
  have e := tsum_lintegral_set_eq (S := Set.univ) (P := P) hξ measurableSet_Icc
    (fun r hr => hr.2 : Set.Icc 0 T ⊆ Set.Iic T)
  simp only [Measure.restrict_univ] at e
  exact e

lemma pc_isCtbl_of (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a))
    (h : ∀ T : ℝ, ∫⁻ ω, (∫⁻ r in Set.Icc 0 T, ∑' a, ‖ξ r ω a‖ₑ ^ 2) ∂P ≠ ⊤) : IsCtbl P ℱ ξ :=
  ⟨hξ, fun T => by rw [pc_tsum_cT hξ]; exact h T⟩

lemma pc_isCtbl_of_le (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) {g : ℝ → Ω → ℝ≥0∞}
    (hg : ∀ r ω, ∑' a, ‖ξ r ω a‖ₑ ^ 2 ≤ g r ω)
    (hfin : ∀ T : ℝ, ∫⁻ ω, (∫⁻ r in Set.Icc 0 T, g r ω) ∂P ≠ ⊤) : IsCtbl P ℱ ξ :=
  pc_isCtbl_of hξ fun T => ne_top_of_le_ne_top (hfin T)
    (lintegral_mono fun ω => lintegral_mono fun r => hg r ω)

lemma pc_isCtbl_of_hasSum_one (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a))
    (h1 : ∀ r ω, HasSum (fun a => ξ r ω a ^ 2) 1) : IsCtbl P ℱ ξ := by
  refine pc_isCtbl_of hξ fun T => ?_
  have : ∀ r ω, ∑' a, ‖ξ r ω a‖ₑ ^ 2 = 1 := fun r ω => by
    rw [enorm_tsum_sq_of_hasSum (h1 r ω)]; simp
  simp [this]

section Comp
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'} {π : Ω' → Ω}

lemma pc_cT_comp (hπp : MeasurePreserving π P' P)
    (hξ : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a)) (a : A) (T : ℝ) :
    cT P' (fun r ω' a => ξ r (π ω') a) a T = cT P ξ a T :=
  hπp.lintegral_comp (measurable_inner_Icc hξ a T)

lemma pc_isCtbl_comp (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) (hπp : MeasurePreserving π P' P)
    (hξ : IsCtbl P ℱ ξ) : IsCtbl P' ℱ' (fun r ω' a => ξ r (π ω') a) :=
  ⟨fun a => isProgressive_comp_π hπm (hξ.prog a), fun T => by
    simp only [pc_cT_comp hπp hξ.prog]; exact hξ.sq T⟩

end Comp
end PC2

section PC3
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ]

lemma pc_isProgressive_ite {β : Type*} [Zero β] [MeasurableSpace β] {u : ℝ → Ω → β}
    (hu : IsProgressive ℱ u) {R : Set ℝ} [DecidablePred (· ∈ R)] (hR : MeasurableSet R) :
    IsProgressive ℱ (fun r ω => if r ∈ R then u r ω else 0) :=
  fun i => Measurable.ite
    (measurable_subtype_coe.comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ i)) hR)
    (hu i) measurable_const

lemma pc_sqIntegralOn_ite_le {ι : Type*} [Fintype ι] (u : ℝ → Ω → ι → ℝ) (R : Set ℝ)
    [DecidablePred (· ∈ R)] (T : ℝ) :
    sqIntegralOn P (fun r ω k => if r ∈ R then u r ω k else 0) T ≤ sqIntegralOn P u T := by
  unfold sqIntegralOn
  refine lintegral_mono fun ω => lintegral_mono fun r => Finset.sum_le_sum fun k _ => ?_
  by_cases h : r ∈ R <;> simp [h]

lemma pc_isProgressiveL2_ite {ι : Type*} [Fintype ι] {u : ℝ → Ω → ι → ℝ}
    (hu : IsProgressiveL2 P ℱ u) {R : Set ℝ} [DecidablePred (· ∈ R)] (hR : MeasurableSet R) :
    IsProgressiveL2 P ℱ (fun r ω k => if r ∈ R then u r ω k else 0) :=
  ⟨by
    have := pc_isProgressive_ite (β := ι → ℝ) hu.prog hR
    convert this using 3 with r ω
    funext k; by_cases h : r ∈ R <;> simp [h],
   fun T => lt_of_le_of_lt (pc_sqIntegralOn_ite_le u R T) (hu.sq T)⟩

lemma pc_enorm_inner_sq_le (a x : H) : ‖inner ℝ a x‖ₑ ^ 2 ≤ ‖a‖ₑ ^ 2 * ‖x‖ₑ ^ 2 := by
  calc ‖inner ℝ a x‖ₑ ^ 2 ≤ (‖a‖ₑ * ‖x‖ₑ) ^ 2 := by
        gcongr; exact enorm_inner_le_enorm a x
    _ = _ := mul_pow _ _ _

lemma pc_sum_inner_sq_le {Φ : κ → H} (F : Finset κ) (x : H) :
    ∑ k ∈ F, ‖inner ℝ (Φ k) x‖ₑ ^ 2 ≤ (∑' k, ‖Φ k‖ₑ ^ 2) * ‖x‖ₑ ^ 2 := by
  calc ∑ k ∈ F, ‖inner ℝ (Φ k) x‖ₑ ^ 2 ≤ ∑ k ∈ F, ‖Φ k‖ₑ ^ 2 * ‖x‖ₑ ^ 2 :=
        Finset.sum_le_sum fun k _ => pc_enorm_inner_sq_le _ _
    _ = (∑ k ∈ F, ‖Φ k‖ₑ ^ 2) * ‖x‖ₑ ^ 2 := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum F

lemma pc_enorm_sq_ne_top (x : H) : ‖x‖ₑ ^ 2 ≠ ⊤ := by
  exact ENNReal.pow_ne_top enorm_ne_top

lemma pc_sqIntegralOn_inner_le {Φ : ℝ → Ω → κ → H} (F : Finset κ) (x : H) (T : ℝ) :
    sqIntegralOn P (fun r ω (k : F) => inner ℝ (Φ r ω k) x) T ≤
      hsSqIntegralOn P Φ T * ‖x‖ₑ ^ 2 := by
  unfold sqIntegralOn hsSqIntegralOn
  rw [← lintegral_mul_const' _ _ (pc_enorm_sq_ne_top x)]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_mul_const' _ _ (pc_enorm_sq_ne_top x)]
  refine lintegral_mono fun r => ?_
  exact (Finset.sum_coe_sort F (fun k => ‖inner ℝ (Φ r ω k) x‖ₑ ^ 2)).le.trans
    (pc_sum_inner_sq_le (Φ := fun k => Φ r ω k) F x)

lemma pc_isProgressiveL2_inner {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H)
    (F : Finset κ) : IsProgressiveL2 P ℱ (fun r ω (k : F) => inner ℝ (Φ r ω k) x) := by
  refine ⟨isProgressive_pi (u := fun (k : F) r ω => inner ℝ (Φ r ω k) x) fun k i =>
    ((hΦ 0).prog k i).inner measurable_const, fun T => ?_⟩
  exact lt_of_le_of_lt (pc_sqIntegralOn_inner_le F x T)
    (ENNReal.mul_lt_top (hΦ T).sq (lt_top_iff_ne_top.2 (pc_enorm_sq_ne_top x)))

lemma pc_ae_ne_zero : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
  rw [ae_iff]; simp

lemma pc_kill_eq {W : ℝ≥0 → Ω → κ → ℝ} (hW : IsCylindricalBrownian P ℱ W) {Φ : ℝ → Ω → κ → H}
    (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H) {t : ℝ} (ht : 0 ≤ t) (F : Finset κ) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ, 0 ≤ τ →
      itoIntegral P ℱ (fun s ω (k : F) => W s ω k)
        (fun r ω (k : F) => if r ≤ t then inner ℝ (Φ r ω k) x else 0) τ ω =
      itoIntegral P ℱ (fun s ω (k : F) => W s ω k) (fun r ω (k : F) => inner ℝ (Φ r ω k) x)
        (min τ t) ω := by
  set u : ℝ → Ω → F → ℝ := fun r ω (k : F) => inner ℝ (Φ r ω k) x with hu
  have hL := pc_isProgressiveL2_inner hΦ x F
  have hW' := hW F
  set g : ℝ → Ω → F → ℝ := fun r ω k => if r ≤ t then u r ω k else 0 with hg
  set ind : ℝ → Ω → F → ℝ := fun s ω => Set.indicator (Set.Ioc 0 t) (fun _ => u s ω) s with hind0
  have hind : ind = fun r ω k => if r ∈ Set.Ioc 0 t then u r ω k else 0 := by
    funext r ω k
    simp only [hind0, Set.indicator_apply]
    split_ifs <;> rfl
  have hLg : IsProgressiveL2 P ℱ g := by
    have := pc_isProgressiveL2_ite hL (measurableSet_Iic (a := t))
    simpa [hg] using this
  have hLind : IsProgressiveL2 P ℱ ind := by
    rw [hind]; exact pc_isProgressiveL2_ite hL measurableSet_Ioc
  have hcong := itoIntegral_congr hW' hLg hLind (fun T => by
    unfold sqIntegralOn
    have hz : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), r ≠ 0 := ae_restrict_of_ae pc_ae_ne_zero
    have hz3 : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), r ∈ Set.Icc 0 T :=
      ae_restrict_mem measurableSet_Icc
    have hz2 : ∀ ω, ∫⁻ r in Set.Icc 0 T, ∑ k, ‖(g r ω - ind r ω) k‖ₑ ^ 2 = 0 := by
      intro ω
      rw [lintegral_congr_ae (g := fun _ => 0)]
      · simp
      · filter_upwards [hz, hz3] with r h1 h2
        have hr : 0 < r := lt_of_le_of_ne h2.1 (Ne.symm h1)
        have : g r ω = ind r ω := by
          rw [hind]; simp only [hg]
          by_cases hrt : r ≤ t
          · simp [hrt, hr]
          · simp [hrt]
        simp [this]
    exact (lintegral_congr hz2).trans lintegral_zero)
  have hI := itoIntegral_indicator_Ioc hW' hL (le_refl 0) ht
  filter_upwards [hcong, hI] with ω h1 h2 τ hτ
  have e1 := h1 τ
  have e2 := h2 τ
  have h0 : itoIntegral P ℱ (fun s ω (k : F) => W s ω k) u (min τ 0) ω = 0 :=
    itoIntegral_of_nonpos _ _ _ _ (min_le_right _ _) ω
  rw [h0, sub_zero] at e2
  exact e1.trans e2

section PC3B
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ℱ' : Filtration ℝ mΩ'} {π : Ω' → Ω}
variable {ι : Type*} [Countable ι]

/-- The killed coordinate integrand `1_{r ≤ t} ⟨Φ_r u_k, x⟩` on `κ ⊕ ι`, supported on `κ`. -/
def pcXi (t : ℝ) (Φ : ℝ → Ω → κ → H) (x : H) (ι : Type*) : ℝ → Ω → κ ⊕ ι → ℝ :=
  fun r ω => Sum.elim (fun k => if r ≤ t then inner ℝ (Φ r ω k) x else 0) (fun _ => 0)

lemma pc_isProgressiveL2_comp (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) (hπp : MeasurePreserving π P' P)
    {s : Type*} [Fintype s] {g : ℝ → Ω → s → ℝ} (hg : IsProgressiveL2 P ℱ g) :
    IsProgressiveL2 P' ℱ' (fun r ω' k => g r (π ω') k) :=
  ⟨isProgressive_comp_π hπm hg.prog, fun T => by
    rw [sqIntegralOn_comp_π hπm hπp hg.prog]; exact hg.sq T⟩

lemma pc_ItoF_pad {𝔚' : ℝ≥0 → Ω' → κ ⊕ ι → ℝ} (h𝔚 : IsCylindricalBrownian P' ℱ' 𝔚')
    (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) (hπp : MeasurePreserving π P' P) {Φ : ℝ → Ω → κ → H}
    (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H) (t : ℝ) (F' : Finset (κ ⊕ ι)) :
    ∀ᵐ ω' ∂P', ∀ τ, ItoF P' ℱ' 𝔚' (fun r ω' => pcXi t Φ x ι r (π ω')) F' τ ω' =
      itoIntegral P' ℱ'
        (fun s ω' (k : F'.preimage Sum.inl Sum.inl_injective.injOn) => 𝔚' s ω' (Sum.inl k))
        (fun r ω' (k : F'.preimage Sum.inl Sum.inl_injective.injOn) =>
          if r ≤ t then inner ℝ (Φ r (π ω') k) x else 0) τ ω' := by
  classical
  set Fκ := F'.preimage Sum.inl Sum.inl_injective.injOn with hFκ
  let ε : Fκ → F' := fun k => ⟨Sum.inl k, Finset.mem_preimage.1 k.2⟩
  have hε : Function.Injective ε := fun a b h =>
    Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
  have hLg : IsProgressiveL2 P' ℱ' (fun r ω' (k : Fκ) =>
      if r ≤ t then inner ℝ (Φ r (π ω') k) x else 0) := by
    have := pc_isProgressiveL2_comp hπm hπp
      (pc_isProgressiveL2_ite (pc_isProgressiveL2_inner hΦ x Fκ) (measurableSet_Iic (a := t)))
    simpa using this
  have h1 := itoIntegral_pad ε hε (W₂ := fun s ω' (a : F') => 𝔚' s ω' a) (h𝔚 F')
    ((h𝔚.comp_inj Sum.inl Sum.inl_injective) Fκ) hLg
  have hpad : padFun ε (fun r ω' (k : Fκ) => if r ≤ t then inner ℝ (Φ r (π ω') k) x else 0) =
      ξF (fun r ω' => pcXi t Φ x ι r (π ω')) F' := by
    funext r ω' a
    obtain ⟨b, hb⟩ := a
    rcases b with k | l
    · have : (⟨Sum.inl k, hb⟩ : F') = ε ⟨k, Finset.mem_preimage.2 hb⟩ := rfl
      simp only [padFun, ξF, pcXi]
      rw [this, padVec_apply ε hε]
      rfl
    · have hn : (⟨Sum.inr l, hb⟩ : F') ∉ Set.range ε := by
        rintro ⟨k, hk⟩
        exact Sum.inl_ne_inr (congrArg Subtype.val hk)
      simp only [padFun, ξF, pcXi]
      rw [padVec_of_notMem ε _ hn]
      rfl
  filter_upwards [h1] with ω' h τ
  show itoIntegral P' ℱ' (WF 𝔚' F') (ξF (fun r ω' => pcXi t Φ x ι r (π ω')) F') τ ω' = _
  rw [← hpad]
  exact (h τ).symm

theorem pc_Z_isItoC {W : ℝ≥0 → Ω → κ → ℝ} (hW : IsCylindricalBrownian P ℱ W)
    {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) {M : ℝ → Ω → H}
    (hM : IsHilbertItoIntegral P ℱ W Φ M) {t : ℝ} (ht : 0 ≤ t)
    (hπm : ∀ s, Measurable[ℱ' s, ℱ s] π) (hπp : MeasurePreserving π P' P)
    {𝔚' : ℝ≥0 → Ω' → κ ⊕ ι → ℝ} (h𝔚 : IsCylindricalBrownian P' ℱ' 𝔚')
    (h𝔚l : ∀ s ω' k, 𝔚' s ω' (Sum.inl k) = W s (π ω') k) (x : H) :
    IsItoC P' ℱ' 𝔚' (fun r ω' => pcXi t Φ x ι r (π ω'))
      (fun τ ω' => inner ℝ (M (min τ t) (π ω')) x) := by
  classical
  refine ⟨fun ω' => ?_, fun τ => ?_, fun τ hτ ω' => ?_, fun τ hτ => ?_⟩
  · exact ((hM.cont (π ω')).comp (continuous_id.min continuous_const)).inner continuous_const
  · have h1 : Measurable[ℱ τ] (M (min τ t)) :=
      (hM.adapted (min τ t)).mono (ℱ.mono (min_le_left τ t)) le_rfl
    exact (h1.inner measurable_const).comp (hπm τ)
  · simp [hM.zero (min τ t) ((min_le_left τ t).trans hτ) (π ω')]
  · have hlim := hM.approx (min τ t) (le_min hτ ht) x
    have hcomp := hlim.comp (tendsto_finset_preimage_atTop_atTop
      (Sum.inl_injective (α := κ) (β := ι)))
    refine hcomp.congr (fun F' => ?_)
    set Fκ := F'.preimage Sum.inl Sum.inl_injective.injOn with hFκ
    simp only [Function.comp_apply]
    -- the functions on Ω
    set u : ℝ → Ω → Fκ → ℝ := fun r ω (k : Fκ) => inner ℝ (Φ r ω k) x with hu
    set gΩ : ℝ → Ω → Fκ → ℝ := fun r ω k => if r ≤ t then u r ω k else 0 with hgΩ
    have hgL : IsProgressiveL2 P ℱ gΩ := by
      have := pc_isProgressiveL2_ite (pc_isProgressiveL2_inner hΦ x Fκ) (measurableSet_Iic (a := t))
      simpa [hgΩ, hu] using this
    have hWF : IsBrownianFiltration P ℱ (fun s ω (k : Fκ) => W s ω k) := hW Fκ
    have hWF' : IsBrownianFiltration P' ℱ' (fun s ω' (k : Fκ) => W s (π ω') k) := by
      have := (h𝔚.comp_inj Sum.inl Sum.inl_injective) Fκ
      have e : (fun s ω' (k : Fκ) => 𝔚' s ω' (Sum.inl (k : κ))) =
          (fun s ω' (k : Fκ) => W s (π ω') k) := by
        funext s ω' k; exact h𝔚l s ω' k
      rw [← e]; exact this
    have hK2 := itoIntegral_comp_π hπm hπp hWF hWF' hgL
    have hK1 := hπp.quasiMeasurePreserving.ae (pc_kill_eq hW hΦ x ht Fκ)
    have hK3 := pc_ItoF_pad h𝔚 hπm hπp hΦ x t F'
    have hWeq : (fun s ω' (k : Fκ) => 𝔚' s ω' (Sum.inl (k : κ))) =
        (fun s ω' (k : Fκ) => W s (π ω') k) := by
      funext s ω' k; exact h𝔚l s ω' k
    have hae : ∀ᵐ ω' ∂P', ‖ItoF P' ℱ' 𝔚' (fun r ω' => pcXi t Φ x ι r (π ω')) F' τ ω' -
          inner ℝ (M (min τ t) (π ω')) x‖ₑ ^ 2 =
        (fun ω => ‖itoIntegral P ℱ (fun s ω (k : Fκ) => W s ω k) u (min τ t) ω -
          inner ℝ (M (min τ t) ω) x‖ₑ ^ 2) (π ω') := by
      filter_upwards [hK3, hK2, hK1] with ω' h3 h2 h1
      rw [h3 τ, hWeq]
      have e := (h2 τ).trans (h1 τ hτ)
      rw [e]
    have hmeas : Measurable (fun ω => ‖itoIntegral P ℱ (fun s ω (k : Fκ) => W s ω k) u (min τ t) ω -
          inner ℝ (M (min τ t) ω) x‖ₑ ^ 2) :=
      ((((adapted_itoIntegral P ℱ (fun s ω (k : Fκ) => W s ω k) u (min τ t)).mono (ℱ.le _) le_rfl).sub
        (((hM.adapted (min τ t)).mono (ℱ.le _) le_rfl).inner measurable_const)).enorm).pow_const 2
    rw [lintegral_congr_ae hae, hπp.lintegral_comp hmeas]

end PC3B
end PC3

section PC4
open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {ι : Type*} [Countable ι]

lemma pc_isCtbl_sub {ξ ξ' : ℝ → Ω → A → ℝ} (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ') :
    IsCtbl P ℱ (fun r ω a => ξ r ω a - ξ' r ω a) := by
  have h := hξ.add (hξ'.mul_bdd (w := fun _ _ => (-1 : ℝ)) (isProgressive_const ℱ _) (C := 1)
    (fun r ω => by simp))
  convert h using 3 with r ω a
  ring

theorem pc_bridge {𝔚 : ℝ≥0 → Ω → A → ℝ} (h𝔚 : IsCylindricalBrownian P ℱ 𝔚)
    {ψ : ι → ℝ → Ω → A → ℝ} (hψ : ∀ j, IsCtbl P ℱ (ψ j))
    {Bj : ι → ℝ → Ω → ℝ} (hB : ∀ j, IsItoC P ℱ 𝔚 (ψ j) (Bj j))
    (hBr : IsCylindricalBrownian P ℱ (fun t ω j => Bj j (t : ℝ) ω))
    (hortho : ∀ r ω i j, HasSum (fun a => ψ i r ω a * ψ j r ω a) (if i = j then (1 : ℝ) else 0))
    {f : ℝ → Ω → ι → ℝ} (hf : IsCtbl P ℱ f)
    {Ξ : ℝ → Ω → A → ℝ} (hΞ : IsCtbl P ℱ Ξ) {Z : ℝ → Ω → ℝ} (hZ : IsItoC P ℱ 𝔚 Ξ Z)
    (hsum : ∀ r ω, Summable fun j => f r ω j ^ 2)
    (hE2 : ∀ (s : Finset ι) r ω, HasSum
      (fun a => (Ξ r ω a - ∑ j ∈ s, f r ω j * ψ j r ω a) ^ 2)
      (∑' j, if j ∈ s then 0 else f r ω j ^ 2))
    (τ : ℝ) (hτ : 0 ≤ τ) :
    Tendsto (fun s : Finset ι => ∫⁻ ω, ‖itoIntegral P ℱ
      (fun t ω (k : s) => (fun t ω j => Bj j (t : ℝ) ω) t ω k) (fun r ω (k : s) => f r ω k) τ ω
        - Z τ ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  have hbound : ∀ s : Finset ι, ∫⁻ ω, ‖itoIntegral P ℱ
      (fun t ω (k : s) => (fun t ω j => Bj j (t : ℝ) ω) t ω k) (fun r ω (k : s) => f r ω k) τ ω
        - Z τ ω‖ₑ ^ 2 ∂P ≤ tailC P f s τ := by
    intro s
    -- the finite-family data
    set ψs : s → ℝ → Ω → A → ℝ := fun j => ψ (j : ι) with hψs
    set fs : ℝ → Ω → s → ℝ := fun r ω (k : s) => f r ω k with hfs
    have hfL : IsProgressiveL2 P ℱ fs := hf.progressiveL2 s
    have hortho_s : ∀ r ω (j j' : s), HasSum (fun a => ψs j r ω a * ψs j' r ω a)
        (@ite ℝ (j = j') (Classical.propDecidable _) 1 0) := fun r ω j j' => by
      have := hortho r ω j j'
      by_cases h : j = j'
      · subst h; simpa using this
      · have h' : (j : ι) ≠ j' := fun e => h (Subtype.ext e)
        simpa [h, h'] using this
    have hψprog : ∀ (j : s) a, IsProgressive ℱ (fun r ω => ψs j r ω a) := fun j a => (hψ j).prog a
    have hΞs : IsCtbl P ℱ (fun r ω a => ∑ j : s, fs r ω j * ψs j r ω a) :=
      isCtbl_comb hψprog hortho_s hfL
    obtain ⟨Y, hY⟩ := exists_isItoC h𝔚 hΞs
    have hassoc := isItoIntegral_assoc (ψ := ψs) h𝔚 (fun j => hψ j) (Bj := fun j => Bj j)
      (fun j => hB j) (hBr s) hortho_s hfL hY
    have hae := IsItoIntegral.ae_eq_forall (hBr s) (isItoIntegral_itoIntegral (hBr s) hfL) hassoc hfL
    have hdiff := IsItoC.sub h𝔚 hΞ hΞs hZ hY
    have hΞd : IsCtbl P ℱ (fun r ω a => Ξ r ω a - ∑ j : s, fs r ω j * ψs j r ω a) :=
      pc_isCtbl_sub hΞ hΞs
    have hsq := hdiff.lintegral_sq_le hΞd h𝔚 hτ
    have hRHS : ∑' a, cT P (fun r ω a => Ξ r ω a - ∑ j : s, fs r ω j * ψs j r ω a) a τ =
        tailC P f s τ := by
      rw [pc_tsum_cT hΞd.prog τ]
      have e : ∀ r ω, ∑' a, ‖Ξ r ω a - ∑ j : s, fs r ω j * ψs j r ω a‖ₑ ^ 2 =
          ∑' j, ‖ξtail f s r ω j‖ₑ ^ 2 := by
        intro r ω
        have hfun : ∀ a, Ξ r ω a - ∑ j : s, fs r ω j * ψs j r ω a =
            Ξ r ω a - ∑ j ∈ s, f r ω j * ψ j r ω a := fun a => by
          rw [Finset.sum_coe_sort s (fun j => f r ω j * ψ j r ω a)]
        have h1 : HasSum (fun a => (Ξ r ω a - ∑ j : s, fs r ω j * ψs j r ω a) ^ 2)
            (∑' j, if j ∈ s then 0 else f r ω j ^ 2) := by
          simp only [hfun]; exact hE2 s r ω
        have hfun2 : (fun j => (ξtail f s r ω j) ^ 2) = fun j => if j ∈ s then 0 else f r ω j ^ 2 := by
          funext j; unfold ξtail; split_ifs <;> simp
        have hs' : Summable (fun j => if j ∈ s then (0 : ℝ) else f r ω j ^ 2) :=
          Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [sq_nonneg])
            (fun j => by split_ifs <;> simp [sq_nonneg]) (hsum r ω)
        have h2 : HasSum (fun j => (ξtail f s r ω j) ^ 2) (∑' j, if j ∈ s then 0 else f r ω j ^ 2) := by
          rw [hfun2]; exact hs'.hasSum
        rw [enorm_tsum_sq_of_hasSum h1, enorm_tsum_sq_of_hasSum h2]
      calc ∫⁻ ω, (∫⁻ r in Set.Icc 0 τ, ∑' a,
              ‖Ξ r ω a - ∑ j : s, fs r ω j * ψs j r ω a‖ₑ ^ 2) ∂P
          = ∫⁻ ω, (∫⁻ r in Set.Icc 0 τ, ∑' j, ‖ξtail f s r ω j‖ₑ ^ 2) ∂P :=
            lintegral_congr fun ω => lintegral_congr fun r => e r ω
        _ = ∑' j, cT P (ξtail f s) j τ := (pc_tsum_cT (isProgressive_ξtail hf.prog s) τ).symm
        _ = tailC P f s τ := tsum_congr fun j => cT_ξtail s j τ
    rw [hRHS] at hsq
    calc ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => (fun t ω j => Bj j (t : ℝ) ω) t ω k)
          (fun r ω (k : s) => f r ω k) τ ω - Z τ ω‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ‖(Z τ ω - Y τ ω)‖ₑ ^ 2 ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω h
          rw [h τ, enorm_sub_rev]
      _ ≤ tailC P f s τ := hsq
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tailC_tendsto hf τ)
    (fun s => bot_le) hbound

end PC4

section PC6
open Classical

/-- A countable dense subset of `[0,N]` (together with the endpoints). -/
def pcD (N : ℝ) : Set ℝ := (Set.Ioo 0 N ∩ Set.range ((↑) : ℚ → ℝ)) ∪ {0, N}

lemma pcD_countable (N : ℝ) : (pcD N).Countable :=
  (((Set.countable_range _).mono Set.inter_subset_right).union
    (Set.toFinite ({0, N} : Set ℝ)).countable)

lemma pcD_subset {N : ℝ} (hN : 0 ≤ N) : pcD N ⊆ Set.Icc 0 N := by
  rintro d (⟨hd, -⟩ | hd)
  · exact ⟨hd.1.le, hd.2.le⟩
  · rcases hd with rfl | rfl
    · exact ⟨le_rfl, hN⟩
    · exact ⟨hN, le_rfl⟩

lemma pc_iSup_icc_eq {I : ℝ → ℝ} (hc : Continuous I) {N : ℝ} (hN : 0 ≤ N) :
    (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I τ‖ₑ) = ⨆ d ∈ pcD N, ‖I d‖ₑ := by
  refine le_antisymm ?_ (biSup_mono (pcD_subset hN))
  set c := ⨆ d ∈ pcD N, ‖I d‖ₑ with hc'
  have hcl : IsClosed {τ | ‖I τ‖ₑ ≤ c} := isClosed_le hc.enorm continuous_const
  have hDsub' : pcD N ⊆ {τ | ‖I τ‖ₑ ≤ c} := fun d hd =>
    le_iSup₂ (f := fun d (_ : d ∈ pcD N) => ‖I d‖ₑ) d hd
  have h1 : closure (pcD N) ⊆ {τ | ‖I τ‖ₑ ≤ c} := closure_minimal hDsub' hcl
  refine iSup₂_le fun τ hτ => ?_
  have : τ ∈ closure (pcD N) := by
    by_cases h0 : τ = 0 ∨ τ = N
    · exact subset_closure (Or.inr (by rcases h0 with h | h <;> simp [h]))
    · push_neg at h0
      have hτ' : τ ∈ Set.Ioo 0 N := ⟨lt_of_le_of_ne hτ.1 (Ne.symm h0.1), lt_of_le_of_ne hτ.2 h0.2⟩
      have := Rat.denseRange_cast.open_subset_closure_inter (isOpen_Ioo (a := (0:ℝ)) (b := N)) hτ'
      exact closure_mono Set.subset_union_left this
  exact h1 this

lemma pc_measurable_iSup_icc {Ω : Type*} [MeasurableSpace Ω] {I : ℝ → Ω → ℝ}
    (hc : ∀ ω, Continuous fun τ => I τ ω) (hm : ∀ τ, Measurable (I τ)) (N : ℝ) :
    Measurable fun ω => ⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I τ ω‖ₑ := by
  rcases lt_or_ge N 0 with hN | hN
  · have : Set.Icc (0 : ℝ) N = ∅ := Set.Icc_eq_empty (not_le.2 hN)
    simp [this]
  · have e : (fun ω => ⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I τ ω‖ₑ) =
        fun ω => ⨆ d ∈ pcD N, ‖I d ω‖ₑ := funext fun ω => pc_iSup_icc_eq (hc ω) hN
    rw [e]
    have : Countable (pcD N) := (pcD_countable N).to_subtype
    have e2 : (fun ω => ⨆ d ∈ pcD N, ‖I d ω‖ₑ) = fun ω => ⨆ d : pcD N, ‖I d ω‖ₑ :=
      funext fun ω => iSup_subtype'
    rw [e2]
    exact Measurable.iSup fun d => (hm d).enorm

section PCVec
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*}

lemma pc_memℓp {c : ι → ℝ} (h : Summable fun i => c i ^ 2) : Memℓp c 2 := by
  refine memℓp_gen ?_
  simpa [Real.rpow_two] using h

/-- The vector `∑ c_i e_i` for a square-summable coefficient family (`0` otherwise). -/
def pcVec (e : HilbertBasis ι ℝ H) (c : ι → ℝ) : H :=
  if h : Summable (fun i => c i ^ 2) then e.repr.symm ⟨c, pc_memℓp h⟩ else 0

lemma pcVec_hasSum (e : HilbertBasis ι ℝ H) {c : ι → ℝ} (h : Summable fun i => c i ^ 2) :
    HasSum (fun i => c i • e i) (pcVec e c) := by
  simp only [pcVec, dif_pos h]
  exact e.hasSum_repr_symm ⟨c, pc_memℓp h⟩

lemma pcVec_inner_basis (e : HilbertBasis ι ℝ H) {c : ι → ℝ} (h : Summable fun i => c i ^ 2)
    (i : ι) : inner ℝ (pcVec e c) (e i) = c i := by
  have := (pcVec_hasSum e h).mapL (innerSL ℝ (e i))
  have h2 : ∀ k, inner ℝ (e i) (c k • e k) = c k * inner ℝ (e i) (e k) := fun k => by
    rw [real_inner_smul_right]
  classical
  have h3 : ∀ k, inner ℝ (e i) (e k) = if i = k then (1:ℝ) else 0 := fun k => by
    rw [orthonormal_iff_ite.1 e.orthonormal]
  simp only [innerSL_apply_apply, h2, h3] at this
  have h4 : ∀ k, c k * (if i = k then (1:ℝ) else 0) = if i = k then c k else 0 := fun k => by
    split_ifs <;> simp
  simp only [h4] at this
  have h5 : HasSum (fun k => if i = k then c k else 0) (c i) := by
    have := hasSum_single (f := fun k => if i = k then c k else 0) i
      (fun k hk => by simp [Ne.symm hk])
    simpa using this
  rw [real_inner_comm]
  exact (this.unique h5)

lemma pcVec_hasSum_sq (e : HilbertBasis ι ℝ H) {c : ι → ℝ} (h : Summable fun i => c i ^ 2) :
    HasSum (fun i => c i ^ 2) (‖pcVec e c‖ ^ 2) := by
  have := e.hasSum_inner_mul_inner (pcVec e c) (pcVec e c)
  rw [real_inner_self_eq_norm_sq] at this
  convert this using 2 with i
  have h6 : inner ℝ (e i) (pcVec e c) = c i := by
    rw [real_inner_comm]; exact pcVec_inner_basis e h i
  rw [h6, pcVec_inner_basis e h i, sq]

lemma pcVec_hasSum_inner (e : HilbertBasis ι ℝ H) {c : ι → ℝ} (h : Summable fun i => c i ^ 2)
    (x : H) : HasSum (fun i => c i * inner ℝ (e i) x) (inner ℝ (pcVec e c) x) := by
  have := (pcVec_hasSum e h).mapL (innerSL ℝ x)
  simp only [innerSL_apply_apply, real_inner_smul_right] at this
  rw [real_inner_comm] at this
  convert this using 2 with i
  rw [real_inner_comm]

lemma pcVec_zero (e : HilbertBasis ι ℝ H) : pcVec e (fun _ => 0) = 0 := by
  have h : Summable fun i : ι => ((fun _ => (0:ℝ)) i) ^ 2 := by simpa using summable_zero
  have := pcVec_hasSum e h
  simp only [zero_smul] at this
  exact this.unique hasSum_zero

lemma summable_sq_sub {c d : ι → ℝ} (hc : Summable fun i => c i ^ 2) (hd : Summable fun i => d i ^ 2) :
    Summable fun i => (c i - d i) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
    ((hc.mul_left 2).add (hd.mul_left 2))
  nlinarith [sq_nonneg (c i + d i)]

lemma pcVec_sub (e : HilbertBasis ι ℝ H) {c d : ι → ℝ} (hc : Summable fun i => c i ^ 2)
    (hd : Summable fun i => d i ^ 2) : pcVec e (fun i => c i - d i) = pcVec e c - pcVec e d := by
  have h1 := (pcVec_hasSum e hc).sub (pcVec_hasSum e hd)
  have h2 := pcVec_hasSum e (summable_sq_sub hc hd)
  simp only [sub_smul] at h2
  exact h2.unique h1

lemma pcVec_finsupp (e : HilbertBasis ι ℝ H) (c : ι → ℝ) (F : Finset ι) :
    pcVec e (fun i => if i ∈ F then c i else 0) = ∑ i ∈ F, c i • e i := by
  classical
  have hs : Summable fun i => ((fun i => if i ∈ F then c i else 0) i) ^ 2 :=
    summable_of_ne_finset_zero (s := F) fun i hi => by simp [hi]
  have h1 := pcVec_hasSum e hs
  have h2 : HasSum (fun i => (if i ∈ F then c i else 0) • e i) (∑ i ∈ F, c i • e i) := by
    have h3 : HasSum (fun i => (if i ∈ F then c i else 0) • e i)
        (∑ i ∈ F, (if i ∈ F then c i else 0) • e i) :=
      hasSum_sum_of_ne_finset_zero (fun i hi => by simp [hi])
    convert h3 using 1
    exact (Finset.sum_congr rfl fun i hi => by simp [hi]).symm
  exact h1.unique h2

lemma pc_tsum_compl_eq (f : ι → ℝ) (F : Finset ι) :
    ∑' b : {x // x ∉ F}, f b = ∑' i, if i ∈ F then 0 else f i := by
  have := tsum_subtype ({x | x ∉ F} : Set ι) f
  rw [show (∑' b : {x // x ∉ F}, f b) = ∑' x : ({x | x ∉ F} : Set ι), f x from rfl, this]
  refine tsum_congr fun i => ?_
  by_cases hi : i ∈ F <;> simp [Set.indicator, hi]

theorem pc_continuous_pcVec (e : HilbertBasis ι ℝ H) (c : ℝ → ι → ℝ)
    (hcont : ∀ i, Continuous fun τ => c τ i) (hzero : ∀ (i : ι) (τ : ℝ), τ ≤ 0 → c τ i = 0)
    (σ : ℕ → ι → ℝ) (hσ0 : ∀ N i, 0 ≤ σ N i) (hσs : ∀ N, Summable fun i => σ N i ^ 2)
    (hb : ∀ (N : ℕ) (i : ι) (τ : ℝ), 0 ≤ τ → τ ≤ N → |c τ i| ≤ σ N i) :
    Continuous fun τ => pcVec e (c τ) := by
  classical
  have hb' : ∀ (N : ℕ) (i : ι) (τ : ℝ), τ ≤ N → |c τ i| ≤ σ N i := fun N i τ hτ => by
    by_cases h0 : 0 ≤ τ
    · exact hb N i τ h0 hτ
    · rw [hzero i τ (not_le.1 h0).le]; simpa using hσ0 N i
  have hs : ∀ τ, Summable fun i => c τ i ^ 2 := fun τ => by
    obtain ⟨N, hN⟩ := exists_nat_ge τ
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) (hσs N)
    rw [← sq_abs (c τ i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb' N i τ hN) 2
  -- the finite-sum approximants
  set D : Finset ι → ℝ → H := fun F τ => ∑ i ∈ F, c τ i • e i with hD
  have hDc : ∀ F, Continuous (D F) := fun F =>
    continuous_finsetSum _ fun i _ => (hcont i).smul continuous_const
  have hdist : ∀ (N : ℕ) (F : Finset ι) (τ : ℝ), τ ≤ N →
      ‖pcVec e (c τ) - D F τ‖ ^ 2 ≤ ∑' i, if i ∈ F then 0 else σ N i ^ 2 := by
    intro N F τ hτ
    have h1 : pcVec e (c τ) - D F τ = pcVec e (fun i => if i ∈ F then 0 else c τ i) := by
      have hsF : Summable fun i => ((fun i => if i ∈ F then c τ i else 0) i) ^ 2 :=
        summable_of_ne_finset_zero (s := F) fun i hi => by simp [hi]
      have := pcVec_sub e (hs τ) hsF
      rw [pcVec_finsupp] at this
      rw [hD]; simp only
      rw [← this]
      congr 1
      funext i
      by_cases hi : i ∈ F <;> simp [hi]
    have hsq : Summable fun i => ((fun i => if i ∈ F then (0:ℝ) else c τ i) i) ^ 2 :=
      Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => by
        by_cases hi : i ∈ F <;> simp [hi, sq_nonneg]) (hs τ)
    rw [h1, ← (pcVec_hasSum_sq e hsq).tsum_eq]
    have hsσ : Summable fun i => if i ∈ F then (0:ℝ) else σ N i ^ 2 :=
      Summable.of_nonneg_of_le (fun i => by by_cases hi : i ∈ F <;> simp [hi, sq_nonneg])
        (fun i => by by_cases hi : i ∈ F <;> simp [hi, sq_nonneg]) (hσs N)
    refine Summable.tsum_le_tsum (fun i => ?_) hsq hsσ
    by_cases hi : i ∈ F
    · simp [hi]
    · simp only [hi, if_false]
      rw [← sq_abs (c τ i)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb' N i τ hτ) 2
  have htail : ∀ N : ℕ, Tendsto (fun F : Finset ι => ∑' i, if i ∈ F then 0 else σ N i ^ 2) atTop
      (𝓝 0) := by
    intro N
    have := tendsto_tsum_compl_atTop_zero (fun i => σ N i ^ 2)
    exact this.congr fun F => pc_tsum_compl_eq (fun i => σ N i ^ 2) F
  have hunif : ∀ N : ℕ, TendstoUniformlyOn D (fun τ => pcVec e (c τ)) atTop
      (Set.Icc (-(N : ℝ)) N) := by
    intro N
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have := (htail N).eventually (gt_mem_nhds (show (0:ℝ) < ε ^ 2 by positivity))
    filter_upwards [this] with F hF τ hτ
    rw [dist_eq_norm]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_le_of_lt (hdist N F τ hτ.2) hF)
  have hcon : ∀ N : ℕ, ContinuousOn (fun τ => pcVec e (c τ)) (Set.Icc (-(N : ℝ)) N) := fun N =>
    (hunif N).continuousOn (Eventually.frequently (Eventually.of_forall fun F => (hDc F).continuousOn))
  rw [continuous_iff_continuousAt]
  intro τ₀
  obtain ⟨N, hN⟩ := exists_nat_gt (|τ₀| + 1)
  have hmem : Set.Icc (-(N : ℝ)) N ∈ 𝓝 τ₀ :=
    Icc_mem_nhds (by linarith [neg_abs_le τ₀]) (by linarith [le_abs_self τ₀])
  exact (hcon N).continuousAt hmem

end PCVec

section PCHv
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

lemma pc_summable_of_enorm_tsum_ne_top {c : ι → ℝ} (h : ∑' i, ‖c i‖ₑ ^ 2 ≠ ⊤) :
    Summable fun i => c i ^ 2 := by
  refine (ENNReal.summable_toReal h).congr fun i => ?_
  rw [enorm_sq_eq_ofReal, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem pc_hvalued (hℱ : IsCompleteFiltration P ℱ) (e : HilbertBasis ι ℝ H)
    (I : ι → ℝ → Ω → ℝ) (hcont : ∀ i ω, Continuous fun τ => I i τ ω)
    (hadapt : ∀ i τ, Measurable[ℱ τ] (I i τ)) (hzero : ∀ i τ, τ ≤ 0 → ∀ ω, I i τ ω = 0)
    (hdoob : ∀ N : ℕ, ∑' i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P ≠ ⊤) :
    ∃ G : ℝ → Ω → H, (∀ ω, Continuous fun τ => G τ ω) ∧ (∀ τ, Measurable[ℱ τ] (G τ)) ∧
      (∀ τ, τ ≤ 0 → ∀ ω, G τ ω = 0) ∧
      ∀ τ, ∀ᵐ ω ∂P, Summable (fun i => I i τ ω ^ 2) ∧ G τ ω = pcVec e (fun i => I i τ ω) := by
  classical
  set s : ι → ℕ → Ω → ℝ≥0∞ := fun i N ω => ⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ with hs
  have hsm : ∀ i N, Measurable (s i N) := fun i N =>
    pc_measurable_iSup_icc (hcont i) (fun τ => (hadapt i τ).mono (ℱ.le τ) le_rfl) N
  set T : ℕ → Ω → ℝ≥0∞ := fun N ω => ∑' i, (s i N ω) ^ 2 with hT
  have hTm : ∀ N, Measurable (T N) := fun N =>
    Measurable.ennreal_tsum fun i => (hsm i N).pow_const 2
  have hTfin : ∀ N, ∫⁻ ω, T N ω ∂P ≠ ⊤ := fun N => by
    simp only [hT]
    rw [lintegral_tsum fun i => ((hsm i N).pow_const 2).aemeasurable]
    exact hdoob N
  have hae : ∀ᵐ ω ∂P, ∀ N, T N ω < ⊤ := ae_all_iff.2 fun N => ae_lt_top (hTm N) (hTfin N)
  set Good : Set Ω := {ω | ∀ N, T N ω < ⊤} with hGood
  have hGoodm : MeasurableSet Good := by
    have : Good = ⋂ N, {ω | T N ω < ⊤} := by ext; simp [hGood]
    rw [this]
    exact MeasurableSet.iInter fun N => measurableSet_lt (hTm N) measurable_const
  have hGoodc : ∀ τ, MeasurableSet[ℱ τ] Good := fun τ =>
    MeasurableSet.of_compl (hℱ τ _ hGoodm.compl (ae_iff.1 hae))
  have hsfin : ∀ ω ∈ Good, ∀ i N, s i N ω ≠ ⊤ := by
    intro ω hω i N hne
    have h1 : (s i N ω) ^ 2 ≤ T N ω := ENNReal.le_tsum (f := fun i => (s i N ω) ^ 2) i
    have h2 : (s i N ω) ^ 2 = ⊤ := by rw [hne]; exact ENNReal.top_pow (by norm_num)
    exact absurd (h2 ▸ h1) (not_le.2 (hω N))
  have hle : ∀ ω (i : ι) (N : ℕ) (τ : ℝ), 0 ≤ τ → τ ≤ N → ‖I i τ ω‖ₑ ≤ s i N ω := fun ω i N τ h0 hN =>
    le_iSup₂ (f := fun τ (_ : τ ∈ Set.Icc (0 : ℝ) N) => ‖I i τ ω‖ₑ) τ ⟨h0, hN⟩
  have hsumm : ∀ ω ∈ Good, ∀ τ, Summable (fun i => I i τ ω ^ 2) := by
    intro ω hω τ
    obtain ⟨N, hN⟩ := exists_nat_ge τ
    refine pc_summable_of_enorm_tsum_ne_top (ne_top_of_le_ne_top (hω N).ne ?_)
    refine ENNReal.tsum_le_tsum fun i => ?_
    by_cases hτ : 0 ≤ τ
    · have := hle ω i N τ hτ hN
      gcongr
    · have : I i τ ω = 0 := hzero i τ (not_le.1 hτ).le ω
      simp [this]
  set G : ℝ → Ω → H := fun τ ω => if ω ∈ Good then pcVec e (fun i => I i τ ω) else 0 with hG
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ Good
    · simp only [hG, hω, ite_true]
      refine pc_continuous_pcVec e (fun τ i => I i τ ω) (fun i => hcont i ω)
        (fun i τ hτ => hzero i τ hτ ω) (fun N i => (s i N ω).toReal) (fun N i => ENNReal.toReal_nonneg)
        (fun N => ?_) (fun N i τ h0 hN => ?_)
      · have := ENNReal.summable_toReal (hω N).ne
        refine this.congr fun i => ?_
        simp [ENNReal.toReal_pow]
      · have h1 := ENNReal.toReal_mono (hsfin ω hω i N) (hle ω i N τ h0 hN)
        rwa [toReal_enorm, Real.norm_eq_abs] at h1
    · have : (fun τ => G τ ω) = fun _ => 0 := by funext τ; simp [hG, hω]
      rw [this]; exact continuous_const
  · intro τ
    letI : MeasurableSpace Ω := ℱ τ
    have hf : ∀ F : Finset ι,
        Measurable (Good.indicator (fun ω => ∑ i ∈ F, I i τ ω • e i)) := fun F =>
      (Finset.measurable_sum _ fun i _ => (hadapt i τ).smul_const (e i)).indicator (hGoodc τ)
    refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι)) hf
      (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ Good
    · simp only [Set.indicator_of_mem hω, hG, hω, ite_true]
      exact pcVec_hasSum e (hsumm ω hω τ)
    · simp only [Set.indicator_of_notMem hω, hG, hω, ite_false]
      exact tendsto_const_nhds
  · intro τ hτ ω
    by_cases hω : ω ∈ Good
    · simp only [hG, hω, ite_true]
      have : (fun i => I i τ ω) = fun _ => 0 := funext fun i => hzero i τ hτ ω
      rw [this]; exact pcVec_zero e
    · simp [hG, hω]
  · intro τ
    filter_upwards [hae] with ω hω
    have hωG : ω ∈ Good := hω
    exact ⟨hsumm ω hωG τ, by simp [hG, hωG]⟩

end PCHv
end PC6

section PC7a

lemma pc_ae_eq_of_limits {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {Y Z : Ω → ℝ} (hX : ∀ n, AEMeasurable (X n) P) (hZ : AEMeasurable Z P)
    (hY : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hXZ : Tendsto (fun n => ∫⁻ ω, ‖X n ω - Z ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) : Y =ᵐ[P] Z := by
  have hYm : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae atTop hX hY
  have h1 : ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P ≤ liminf (fun n => ∫⁻ ω, ‖X n ω - Z ω‖ₑ ^ 2 ∂P) atTop := by
    calc ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P = ∫⁻ ω, liminf (fun n => ‖X n ω - Z ω‖ₑ ^ 2) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hY] with ω hω
          have : Tendsto (fun n => ‖X n ω - Z ω‖ₑ ^ 2) atTop (𝓝 (‖Y ω - Z ω‖ₑ ^ 2)) :=
            ((ENNReal.continuous_pow 2).tendsto _).comp
              ((continuous_enorm.tendsto _).comp (hω.sub_const (Z ω)))
          exact this.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le' fun n => ((hX n).sub hZ).enorm.pow_const 2
  rw [hXZ.liminf_eq] at h1
  have h0 : ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P = 0 := le_antisymm h1 bot_le
  filter_upwards [ae_eq_zero_of_lintegral_enorm_sq_eq_zero (hYm.sub hZ) h0] with ω h
  simpa [sub_eq_zero] using h

end PC7a

section PC7
open Classical HilbertCLTAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- Data for a deterministic operator-valued integrand `Sb` on `[0,t]` against `B`. -/
structure PCDetData (e : HilbertBasis ι ℝ H) (t : ℝ) (Sb : ℝ → H →L[ℝ] H) (T : ℝ → ℝ) : Prop where
  meas : OpMeas Sb
  zero : ∀ r, r ∉ Set.Icc 0 t → Sb r = 0
  parseval : ∀ r x, HasSum (fun j => inner ℝ (Sb r (e j)) x ^ 2) (‖Sb r x‖ ^ 2)
  bound : ∀ r ∈ Set.Icc 0 t, ∀ x, ‖Sb r x‖ ^ 2 ≤ T r * ‖x‖ ^ 2
  trace : ∀ r ∈ Set.Icc 0 t, HasSum (fun i => ‖Sb r (e i)‖ ^ 2) (T r)
  Tmeas : Measurable T
  Tnonneg : ∀ r ∈ Set.Icc 0 t, 0 ≤ T r
  Tint : IntegrableOn T (Set.Icc 0 t)

/-- The deterministic integrand `1_{r ≤ t} ⟨Sb_r e_j, x⟩`. -/
def fSb (e : HilbertBasis ι ℝ H) (t : ℝ) (Sb : ℝ → H →L[ℝ] H) (x : H) :
    ℝ → Ω → ι → ℝ := fun r _ j => if r ≤ t then inner ℝ (Sb r (e j)) x else 0

variable {e : HilbertBasis ι ℝ H} {t : ℝ} {Sb : ℝ → H →L[ℝ] H} {T : ℝ → ℝ}

lemma PCDetData.prog (hD : PCDetData e t Sb T) (x : H) (j : ι) :
    IsProgressive ℱ (fun r ω => fSb (Ω := Ω) e t Sb x r ω j) :=
  pc_isProgressive_det (g := fun r => if r ≤ t then inner ℝ (Sb r (e j)) x else 0)
    (Measurable.ite measurableSet_Iic ((hD.meas (e j)).inner measurable_const) measurable_const)

lemma PCDetData.tsum_eq (hD : PCDetData e t Sb T) (x : H) (r : ℝ) (ω : Ω) :
    ∑' j, ‖fSb e t Sb x r ω j‖ₑ ^ 2 = ENNReal.ofReal (if r ≤ t then ‖Sb r x‖ ^ 2 else 0) := by
  by_cases hr : r ≤ t
  · simp only [fSb, hr, ite_true]
    exact enorm_tsum_sq_of_hasSum (hD.parseval r x)
  · simp [fSb, hr]

lemma PCDetData.tsum_le (hD : PCDetData e t Sb T) (x : H) (r : ℝ) (ω : Ω) :
    ∑' j, ‖fSb e t Sb x r ω j‖ₑ ^ 2 ≤
      ENNReal.ofReal ((Set.Icc 0 t).indicator (fun r => T r * ‖x‖ ^ 2) r) := by
  rw [hD.tsum_eq x r ω]
  by_cases hr : r ∈ Set.Icc 0 t
  · rw [Set.indicator_of_mem hr]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hr.2, ite_true]
    exact hD.bound r hr x
  · rw [Set.indicator_of_notMem hr, hD.zero r hr]
    simp

lemma PCDetData.lintegral_bound_lt (hD : PCDetData e t Sb T) (x : H) (N : ℝ) :
    ∫⁻ r in Set.Icc 0 N, ENNReal.ofReal ((Set.Icc 0 t).indicator (fun r => T r * ‖x‖ ^ 2) r) < ⊤ := by
  have h1 : Integrable ((Set.Icc 0 t).indicator (fun r => T r * ‖x‖ ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 (hD.Tint.mul_const _)
  exact h1.integrableOn.lintegral_lt_top

lemma PCDetData.ctbl (hD : PCDetData e t Sb T) (x : H) :
    IsCtbl P ℱ (fSb (Ω := Ω) e t Sb x) :=
  pc_isCtbl_of_le (hD.prog x)
    (g := fun r _ => ENNReal.ofReal ((Set.Icc 0 t).indicator (fun r => T r * ‖x‖ ^ 2) r))
    (fun r ω => hD.tsum_le x r ω) (fun N => by
      rw [lintegral_const, measure_univ, mul_one]
      exact (hD.lintegral_bound_lt x N).ne)

lemma PCDetData.lintegral_T_lt (hD : PCDetData e t Sb T) (N : ℝ) :
    ∫⁻ r in Set.Icc 0 N, ENNReal.ofReal ((Set.Icc 0 t).indicator T r) < ⊤ := by
  have h1 : Integrable ((Set.Icc 0 t).indicator T) volume :=
    (integrable_indicator_iff measurableSet_Icc).2 hD.Tint
  exact h1.integrableOn.lintegral_lt_top

lemma PCDetData.tsum_cT_eq (ℱ' : Filtration ℝ mΩ) (hD : PCDetData e t Sb T) (x : H) (N : ℝ) :
    ∑' j, cT P (fSb (Ω := Ω) e t Sb x) j N =
      ∫⁻ r in Set.Icc 0 N, ENNReal.ofReal (if r ≤ t then ‖Sb r x‖ ^ 2 else 0) := by
  rw [pc_tsum_cT (ℱ := ℱ') (hD.prog x) N]
  simp_rw [hD.tsum_eq x]
  rw [lintegral_const, measure_univ, mul_one]

lemma PCDetData.sum_trace_le (hD : PCDetData e t Sb T) (r : ℝ) :
    ∑' i, ENNReal.ofReal (if r ≤ t then ‖Sb r (e i)‖ ^ 2 else 0) ≤
      ENNReal.ofReal ((Set.Icc 0 t).indicator T r) := by
  by_cases hr : r ∈ Set.Icc 0 t
  · rw [Set.indicator_of_mem hr]
    simp only [hr.2, ite_true]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (hD.trace r hr).summable,
      (hD.trace r hr).tsum_eq]
  · rw [Set.indicator_of_notMem hr]
    have : ∀ i, (if r ≤ t then ‖Sb r (e i)‖ ^ 2 else 0) = 0 := fun i => by
      by_cases h : r ≤ t
      · have : r < 0 := by
          by_contra h0
          exact hr ⟨not_lt.1 h0, h⟩
        simp [hD.zero r hr]
      · simp [h]
    simp [this]

lemma PCDetData.doob_sum (hD : PCDetData e t Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) {I : ι → ℝ → Ω → ℝ}
    (hI : ∀ i, IsItoC P ℱ B (fSb e t Sb (e i)) (I i)) (N : ℕ) :
    ∑' i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P ≠ ⊤ := by
  have hterm : ∀ i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P ≤
      4 * ∫⁻ r in Set.Icc 0 (N : ℝ), ENNReal.ofReal (if r ≤ t then ‖Sb r (e i)‖ ^ 2 else 0) := by
    intro i
    have hM : Martingale (I i) ℱ P := (hI i).martingale (hD.ctbl _) hB
    have hL2 : ∀ τ, MemLp (I i τ) 2 P := fun τ => by
      by_cases hτ : 0 ≤ τ
      · exact (hI i).memLp (hD.ctbl _) hB hτ
      · have : I i τ = fun _ => 0 := funext fun ω => (hI i).zero τ (not_le.1 hτ).le ω
        rw [this]; exact MemLp.zero
    have h1 := SimpleIntegrand.doob_L2_continuous hM (hI i).cont hL2 (N : ℝ)
    have h2 := (hI i).lintegral_sq_le (hD.ctbl _) hB (Nat.cast_nonneg N)
    rw [hD.tsum_cT_eq ℱ] at h2
    exact h1.trans (by gcongr)
  refine ne_top_of_le_ne_top (b := 4 * ∫⁻ r in Set.Icc 0 (N : ℝ),
    ENNReal.ofReal ((Set.Icc 0 t).indicator T r)) ?_ ?_
  · exact ENNReal.mul_ne_top (by norm_num) (hD.lintegral_T_lt N).ne
  calc ∑' i, ∫⁻ ω, (⨆ τ ∈ Set.Icc (0 : ℝ) N, ‖I i τ ω‖ₑ) ^ 2 ∂P
      ≤ ∑' i, 4 * ∫⁻ r in Set.Icc 0 (N : ℝ), ENNReal.ofReal (if r ≤ t then ‖Sb r (e i)‖ ^ 2 else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = 4 * ∫⁻ r in Set.Icc 0 (N : ℝ), ∑' i, ENNReal.ofReal (if r ≤ t then ‖Sb r (e i)‖ ^ 2 else 0) := by
        rw [ENNReal.tsum_mul_left, lintegral_tsum]
        intro i
        refine (Measurable.ennreal_ofReal ?_).aemeasurable
        exact Measurable.ite measurableSet_Iic (((hD.meas (e i)).norm).pow_const 2) measurable_const
    _ ≤ _ := by
        gcongr with r
        exact hD.sum_trace_le r

lemma PCDetData.scalar_le (hD : PCDetData e t Sb T) (z : H) (r : ℝ) :
    ENNReal.ofReal (if r ≤ t then ‖Sb r z‖ ^ 2 else 0) ≤
      ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal ((Set.Icc 0 t).indicator T r) := by
  by_cases hr : r ∈ Set.Icc 0 t
  · rw [Set.indicator_of_mem hr, ← ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [hr.2, ite_true]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖Sb r z‖ ^ 2 ≤ T r * ‖z‖ ^ 2 := hD.bound r hr z
      _ = ‖z‖ ^ 2 * T r := mul_comm _ _
  · rw [Set.indicator_of_notMem hr]
    have : (if r ≤ t then ‖Sb r z‖ ^ 2 else 0) = 0 := by
      by_cases h : r ≤ t
      · have : r < 0 := by
          by_contra h0
          exact hr ⟨not_lt.1 h0, h⟩
        simp [hD.zero r hr]
      · simp [h]
    simp [this]

lemma fSb_comb (e : HilbertBasis ι ℝ H) (t : ℝ) (Sb : ℝ → H →L[ℝ] H) (c : ι → ℝ) (F : Finset ι)
    (x : H) (r : ℝ) (ω : Ω) (j : ι) :
    ∑ i ∈ F, c i * fSb e t Sb (e i) r ω j - fSb e t Sb x r ω j =
      fSb e t Sb (∑ i ∈ F, c i • e i - x) r ω j := by
  by_cases h : r ≤ t
  · simp [fSb, h, inner_sub_right, inner_sum, inner_smul_right]
  · simp [fSb, h]

lemma PCDetData.comb_tendsto (hD : PCDetData e t Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) {I : ι → ℝ → Ω → ℝ}
    (hI : ∀ i, IsItoC P ℱ B (fSb e t Sb (e i)) (I i)) {J : ℝ → Ω → ℝ} (x : H)
    (hJ : IsItoC P ℱ B (fSb e t Sb x) J) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun F : Finset ι => ∫⁻ ω, ‖(∑ i ∈ F, inner ℝ (e i) x * I i τ ω) - J τ ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
  set c : ι → ℝ := fun i => inner ℝ (e i) x with hc
  have hcomb : ∀ F : Finset ι, ∫⁻ ω, ‖(∑ i ∈ F, c i * I i τ ω) - J τ ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (‖∑ i ∈ F, c i • e i - x‖ ^ 2) *
        ∫⁻ r in Set.Icc 0 τ, ENNReal.ofReal ((Set.Icc 0 t).indicator T r) := by
    intro F
    obtain ⟨hξF, hIF⟩ := IsItoC.finset_sum hB F (fun i => fun r ω j => c i * fSb e t Sb (e i) r ω j)
      (fun i => fun τ ω => c i * I i τ ω)
      (fun i _ => (hD.ctbl (Ω := Ω) (ℱ := ℱ) (e i)).mul_bdd (w := fun _ _ => c i)
        (isProgressive_const ℱ _) (C := |c i|) (fun r ω => le_rfl))
      (fun i _ => (hI i).smul hB (hD.ctbl (e i)) (c i))
    have hdiff := IsItoC.sub hB hξF (hD.ctbl x) hIF hJ
    have hΞd := pc_isCtbl_sub hξF (hD.ctbl (Ω := Ω) (ℱ := ℱ) x)
    have h1 := hdiff.lintegral_sq_le hΞd hB hτ
    have hfun : (fun r (ω : Ω) j => ∑ i ∈ F, c i * fSb e t Sb (e i) r ω j - fSb e t Sb x r ω j) =
        fSb e t Sb (∑ i ∈ F, c i • e i - x) := by
      funext r ω j; exact fSb_comb e t Sb c F x r ω j
    rw [hfun, hD.tsum_cT_eq ℱ] at h1
    refine h1.trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun r => hD.scalar_le _ r
  have hlim : Tendsto (fun F : Finset ι => ‖∑ i ∈ F, c i • e i - x‖) atTop (𝓝 0) := by
    have h2 : HasSum (fun i => c i • e i) x := by
      have := e.hasSum_repr x
      convert this using 2 with i
      simp [hc, HilbertBasis.repr_apply_apply]
    exact tendsto_iff_norm_sub_tendsto_zero.1 (show Tendsto (fun F : Finset ι => ∑ i ∈ F, c i • e i)
      atTop (𝓝 x) from h2)
  have hK : ∫⁻ r in Set.Icc 0 τ, ENNReal.ofReal ((Set.Icc 0 t).indicator T r) ≠ ⊤ :=
    (hD.lintegral_T_lt τ).ne
  have hlim2 : Tendsto (fun F : Finset ι => ENNReal.ofReal (‖∑ i ∈ F, c i • e i - x‖ ^ 2) *
      ∫⁻ r in Set.Icc 0 τ, ENNReal.ofReal ((Set.Icc 0 t).indicator T r)) atTop (𝓝 0) := by
    have h3 : Tendsto (fun F : Finset ι => ENNReal.ofReal (‖∑ i ∈ F, c i • e i - x‖ ^ 2)) atTop
        (𝓝 0) := by
      have := (ENNReal.continuous_ofReal.tendsto (0 ^ 2 : ℝ)).comp (hlim.pow 2)
      have e0 : ENNReal.ofReal ((0 : ℝ) ^ 2) = 0 := by simp
      rw [e0] at this
      exact this
    have := ENNReal.Tendsto.mul_const h3 (Or.inr hK)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim2 (fun F => bot_le) hcomb

theorem pc_exists_G (hD : PCDetData e t Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) :
    ∃ G : ℝ → Ω → H,
      IsHilbertItoIntegral P ℱ B (fun r (_ : Ω) j => if r ≤ t then Sb r (e j) else 0) G ∧
      ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ B (fSb e t Sb x) J ∧
        ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (G τ ω) x) =ᵐ[P] J τ := by
  classical
  have hex : ∀ i, ∃ J, IsItoC P ℱ B (fSb e t Sb (e i)) J := fun i => exists_isItoC hB (hD.ctbl _)
  choose I hI using hex
  obtain ⟨G, hGc, hGa, hG0, hGae⟩ := pc_hvalued (hB ∅).complete e I (fun i ω => (hI i).cont ω)
    (fun i τ => (hI i).adapted τ) (fun i τ hτ ω => (hI i).zero τ hτ ω) (hD.doob_sum hB hI)
  have hJex : ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ B (fSb e t Sb x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (G τ ω) x) =ᵐ[P] J τ := by
    intro x
    obtain ⟨J, hJ⟩ := exists_isItoC hB (hD.ctbl (Ω := Ω) (ℱ := ℱ) x)
    refine ⟨J, hJ, fun τ hτ => ?_⟩
    obtain ⟨F, hF⟩ := exists_finset_seq (A := ι)
    have hImeas : ∀ i, Measurable (I i τ) := fun i => ((hI i).adapted τ).mono (ℱ.le τ) le_rfl
    refine pc_ae_eq_of_limits (X := fun n ω => ∑ i ∈ F n, inner ℝ (e i) x * I i τ ω)
      (fun n => (Finset.measurable_sum _ fun i _ => (hImeas i).const_mul _).aemeasurable)
      (((hJ.adapted τ).mono (ℱ.le τ) le_rfl).aemeasurable) ?_ ?_
    · filter_upwards [hGae τ] with ω hω
      obtain ⟨hsum, hGω⟩ := hω
      have := pcVec_hasSum_inner e hsum x
      rw [← hGω] at this
      have h2 : Tendsto (fun s : Finset ι => ∑ i ∈ s, I i τ ω * inner ℝ (e i) x) atTop
          (𝓝 (inner ℝ (G τ ω) x)) := this
      simp only [mul_comm (inner ℝ (e _) x)]
      exact h2.comp hF
    · exact (hD.comb_tendsto hB hI x hJ hτ).comp hF
  choose J hJ using hJex
  refine ⟨G, ⟨hGc, hGa, hG0, fun τ hτ x => ?_⟩, fun x => ⟨J x, (hJ x).1, (hJ x).2⟩⟩
  have hlim := (hJ x).1.approx τ hτ
  refine hlim.congr (fun F => lintegral_congr_ae ?_)
  filter_upwards [(hJ x).2 τ hτ] with ω h
  have hItoF : ItoF P ℱ B (fSb e t Sb x) F =
      itoIntegral P ℱ (fun t ω (k : F) => B t ω k)
        (fun r ω (k : F) => inner ℝ ((fun r (_ : Ω) j => if r ≤ t then Sb r (e j) else 0) r ω k) x) := by
    unfold ItoF WF ξF
    congr 1
    funext r ω k
    by_cases hr : r ≤ t <;> simp [fSb, hr]
  rw [hItoF]
  show ‖itoIntegral P ℱ (fun t ω (k : F) => B t ω k)
        (fun r ω (k : F) => inner ℝ ((fun r (_ : Ω) j => if r ≤ t then Sb r (e j) else 0) r ω k) x) τ ω
      - J x τ ω‖ₑ ^ 2 = _
  rw [← h]

end PC7

section PC8
open Classical

lemma pc_Gint_eq {g : ℝ → ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgm : Measurable g) {τ : ℝ} :
    Gint g τ = ∫ r in Set.Ioc 0 τ, g r := by
  unfold Gint
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm.aestronglyMeasurable]

lemma pc_Gint_continuousOn {g : ℝ → ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgm : Measurable g) {t : ℝ}
    (ht : 0 ≤ t) (hint : IntegrableOn g (Set.Icc 0 t)) : ContinuousOn (Gint g) (Set.Icc 0 t) := by
  have h1 : ContinuousOn (fun b => ∫ x in (0 : ℝ)..b, g x) (Set.uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval'
      (IntegrableOn.intervalIntegrable (by rwa [Set.uIcc_of_le ht])) (by simp [ht])
  rw [Set.uIcc_of_le ht] at h1
  refine h1.congr fun τ hτ => ?_
  rw [pc_Gint_eq hg0 hgm]
  exact (intervalIntegral.integral_of_le hτ.1).symm

lemma pc_Gint_monotoneOn {g : ℝ → ℝ} (hg0 : ∀ r, 0 ≤ g r) (hgm : Measurable g) {t : ℝ}
    (hint : IntegrableOn g (Set.Icc 0 t)) : MonotoneOn (Gint g) (Set.Icc 0 t) := by
  intro a ha b hb hab
  rw [pc_Gint_eq hg0 hgm, pc_Gint_eq hg0 hgm]
  refine setIntegral_mono_set (hint.mono_set (fun r hr => ⟨hr.1.le, hr.2.trans hb.2⟩))
    (Eventually.of_forall hg0) ?_
  exact (Set.Ioc_subset_Ioc_right hab).eventuallyLE

section PC8b
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}

theorem pc_law_cond {M : ℝ → Ω → ℝ} {t : ℝ} (ht : 0 ≤ t) {a : ℝ → ℝ}
    (hMart : Martingale M ℱ P) (hcont : ∀ ω, Continuous fun τ => M τ ω) (hzero : ∀ ω, M 0 ω = 0)
    (hL2 : ∀ τ, MemLp (M τ) 2 P)
    (hMa : Martingale (fun τ ω => M τ ω ^ 2 - a τ) ℱ P) (ha0 : a 0 = 0)
    (hac : ContinuousOn a (Set.Icc 0 t)) (ham : MonotoneOn a (Set.Icc 0 t)) {A0 : Set Ω}
    (hA0 : MeasurableSet[ℱ 0] A0) (hP0 : P A0 ≠ 0) :
    law (ProbabilityTheory.cond P A0) (M t) = gaussianLaw (a t) := by
  haveI : IsProbabilityMeasure (ProbabilityTheory.cond P A0) :=
    ProbabilityTheory.cond_isProbabilityMeasure hP0
  set Q := ProbabilityTheory.cond P A0 with hQ
  have hMQ : Martingale M ℱ Q :=
    martingale_cond P hMart (Eventually.of_forall hzero) hA0 hP0
  have hMaQ : Martingale (fun τ ω => M τ ω ^ 2 - a τ) ℱ Q :=
    martingale_cond P hMa (Eventually.of_forall fun ω => by simp [hzero ω, ha0]) hA0 hP0
  have hQP : Q ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  have hcsm : IsContSqMartingale Q ℱ t M :=
    ⟨hMQ, Eventually.of_forall hzero, Eventually.of_forall fun ω => (hcont ω).continuousOn,
      fun τ _ => ((hL2 τ).restrict A0).smul_measure (ENNReal.inv_ne_top.2 hP0)⟩
  have hqv : IsQuadraticVariation Q ℱ t M (fun τ _ => a τ) :=
    ⟨fun τ => measurable_const, Eventually.of_forall fun _ => ha0,
      Eventually.of_forall fun _ => hac, Eventually.of_forall fun _ => ham, hMaQ⟩
  have hat : 0 ≤ a t := by
    have := ham ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
    rwa [ha0] at this
  obtain ⟨Ω'', _, P'', hP'', M', A', β, hM'm, hA'm, -, hjoint, hid, hlaw, -⟩ :=
    dds_coupling_strong Q ℱ t ht M (fun τ _ => a τ) hcsm hqv (integrable_const _) (a t) hat
  have hMm : Measurable (M t) := (hMart.1 t).measurable.mono (ℱ.le t) le_rfl
  have hpair : Measurable (fun ω' => (M' ω', A' ω')) := hM'm.prodMk hA'm
  have hms : MeasurableSet {p : ℝ × ℝ | ¬ p.2 = a t} :=
    (measurableSet_eq_fun measurable_snd measurable_const).compl
  have hA'ae : ∀ᵐ ω' ∂P'', A' ω' = a t := by
    rw [ae_iff]
    have h1 : P'' {ω' | ¬ A' ω' = a t} = (law P'' (fun ω' => (M' ω', A' ω')))
        {p : ℝ × ℝ | ¬ p.2 = a t} := by
      unfold law
      rw [Measure.map_apply hpair hms]
      rfl
    rw [h1, hjoint]
    unfold law
    rw [Measure.map_apply (hMm.prodMk measurable_const) hms]
    simp
  have hae : M' =ᵐ[P''] β (Real.toNNReal (a t)) := by
    filter_upwards [hid, hA'ae] with ω h1 h2
    rw [h1, h2]
  calc law Q (M t) = (law P'' (fun ω' => (M' ω', A' ω'))).map Prod.fst := by
        rw [hjoint]; unfold law
        rw [Measure.map_map measurable_fst (hMm.prodMk measurable_const)]
        rfl
    _ = law P'' M' := by
        unfold law
        rw [Measure.map_map measurable_fst hpair]
        rfl
    _ = law P'' (β (Real.toNNReal (a t))) := Measure.map_congr hae
    _ = gaussianLaw (a t) := hlaw

end PC8b
end PC8

section PC9
open Classical HilbertCLTAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {e : HilbertBasis ι ℝ H} {t : ℝ} {Sb : ℝ → H →L[ℝ] H} {T : ℝ → ℝ}

lemma pc_ext_of_marginals {μ ν : Measure H} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x : H, μ.map (fun z => inner ℝ x z) = ν.map (fun z => inner ℝ x z)) : μ = ν := by
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  set y := (InnerProductSpace.toDual ℝ H).symm L with hy
  have hL : (L : H → ℝ) = fun z => inner ℝ y z := by
    funext z; rw [hy, InnerProductSpace.toDual_symm_apply]
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hL, h y]

/-- The deterministic bracket integrand `1_{r ≤ t} ‖Sb_r x‖²`. -/
def gSb (t : ℝ) (Sb : ℝ → H →L[ℝ] H) (x : H) : ℝ → ℝ := fun r => if r ≤ t then ‖Sb r x‖ ^ 2 else 0

lemma gSb_nonneg (x : H) (r : ℝ) : 0 ≤ gSb t Sb x r := by
  unfold gSb; split_ifs <;> positivity

lemma PCDetData.gSb_meas (hD : PCDetData e t Sb T) (x : H) : Measurable (gSb t Sb x) :=
  Measurable.ite measurableSet_Iic (((hD.meas x).norm).pow_const 2) measurable_const

lemma PCDetData.gSb_int (hD : PCDetData e t Sb T) (x : H) :
    IntegrableOn (gSb t Sb x) (Set.Icc 0 t) := by
  refine (hD.Tint.mul_const (‖x‖ ^ 2)).mono' (hD.gSb_meas x).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_of_nonneg (gSb_nonneg x r)]
  simp only [gSb, hr.2, ite_true]
  exact hD.bound r hr x

lemma PCDetData.law_J (hD : PCDetData e t Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) {x : H} {J : ℝ → Ω → ℝ}
    (hJ : IsItoC P ℱ B (fSb e t Sb x) J) (ht : 0 ≤ t) {A0 : Set Ω}
    (hA0 : MeasurableSet[ℱ 0] A0) (hP0 : P A0 ≠ 0) :
    law (ProbabilityTheory.cond P A0) (J t) = gaussianLaw (Gint (gSb t Sb x) t) := by
  have hL2 : ∀ τ, MemLp (J τ) 2 P := fun τ => by
    by_cases hτ : 0 ≤ τ
    · exact hJ.memLp (hD.ctbl _) hB hτ
    · have : J τ = fun _ => 0 := funext fun ω => hJ.zero τ (not_le.1 hτ).le ω
      rw [this]; exact MemLp.zero
  exact pc_law_cond ht (hJ.martingale (hD.ctbl x) hB) hJ.cont (fun ω => hJ.zero 0 le_rfl ω) hL2
    (hJ.martingale_sq_sub hB (hD.ctbl x) (fun r ω => hD.tsum_eq x r ω))
    (Gint_of_nonpos _ le_rfl)
    (pc_Gint_continuousOn (gSb_nonneg (t := t) (Sb := Sb) x) (hD.gSb_meas x) ht (hD.gSb_int x))
    (pc_Gint_monotoneOn (gSb_nonneg (t := t) (Sb := Sb) x) (hD.gSb_meas x) (hD.gSb_int x)) hA0 hP0

lemma PCDetData.v_eq (hD : PCDetData e t Sb T) (z : H) :
    Gint (gSb t Sb z) t = ∫ r in Set.Icc 0 t, ‖Sb r z‖ ^ 2 := by
  rw [pc_Gint_eq (gSb_nonneg z) (hD.gSb_meas z), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp [gSb, hr.2]

lemma PCDetData.norm_sq_int (hD : PCDetData e t Sb T) (z : H) :
    IntegrableOn (fun r => ‖Sb r z‖ ^ 2) (Set.Icc 0 t) := by
  refine (hD.gSb_int z).congr_fun (fun r hr => ?_) measurableSet_Icc
  simp [gSb, hr.2]

theorem pc_G_gaussian (hD : PCDetData e t Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) {G : ℝ → Ω → H}
    (hG : ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ B (fSb e t Sb x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (G τ ω) x) =ᵐ[P] J τ)
    (ht : 0 ≤ t) (hGm : Measurable (G t)) (𝒢 : InitialSigma ℱ) :
    Indep 𝒢.1 (MeasurableSpace.comap (G t) inferInstance) P ∧
      IsCenteredGaussian (law P (G t)) ∧
      ∀ x y, covarianceBilin (law P (G t)) x y = ∫ r in Set.Icc 0 t, inner ℝ (Sb r x) (Sb r y) := by
  classical
  set v : H → ℝ := fun x => Gint (gSb t Sb x) t with hv
  have hv0 : ∀ x, 0 ≤ v x := fun x => ENNReal.toReal_nonneg
  have hmarg : ∀ x : H, ∀ A0 : Set Ω, MeasurableSet[ℱ 0] A0 → P A0 ≠ 0 →
      (ProbabilityTheory.cond P A0).map (fun ω => inner ℝ x (G t ω)) = gaussianLaw (v x) := by
    intro x A0 hA0 hP0
    obtain ⟨J, hJ, hae⟩ := hG x
    haveI : IsProbabilityMeasure (ProbabilityTheory.cond P A0) :=
      ProbabilityTheory.cond_isProbabilityMeasure hP0
    have hQP : ProbabilityTheory.cond P A0 ≪ P := ProbabilityTheory.cond_absolutelyContinuous
    have h1 : (fun ω => inner ℝ x (G t ω)) =ᵐ[ProbabilityTheory.cond P A0] J t := by
      filter_upwards [hQP.ae_le (hae t ht)] with ω h
      rw [real_inner_comm]; exact h
    rw [Measure.map_congr h1]
    exact hD.law_J hB hJ ht hA0 hP0
  have hmargP : ∀ x : H, P.map (fun ω => inner ℝ x (G t ω)) = gaussianLaw (v x) := by
    intro x
    have := hmarg x Set.univ MeasurableSet.univ (by simp)
    rwa [ProbabilityTheory.cond_univ] at this
  have hlawQ : ∀ A0 : Set Ω, MeasurableSet[ℱ 0] A0 → P A0 ≠ 0 →
      (ProbabilityTheory.cond P A0).map (G t) = P.map (G t) := by
    intro A0 hA0 hP0
    haveI := ProbabilityTheory.cond_isProbabilityMeasure hP0
    haveI : IsProbabilityMeasure (P.map (G t)) := (Measure.isProbabilityMeasure_map_iff hGm.aemeasurable).2 inferInstance
    haveI : IsProbabilityMeasure ((ProbabilityTheory.cond P A0).map (G t)) :=
      (Measure.isProbabilityMeasure_map_iff hGm.aemeasurable).2 inferInstance
    refine pc_ext_of_marginals fun x => ?_
    have hm1 : Measurable (fun z : H => inner ℝ x z) := measurable_const.inner measurable_id
    rw [Measure.map_map hm1 hGm, Measure.map_map hm1 hGm]
    exact (hmarg x A0 hA0 hP0).trans (hmargP x).symm
  have hindep : Indep 𝒢.1 (MeasurableSpace.comap (G t) inferInstance) P := by
    rw [Indep_iff]
    rintro A S hA ⟨Bset, hBm, rfl⟩
    have hA0 : MeasurableSet[ℱ 0] A := 𝒢.2 _ hA
    have hAm : MeasurableSet A := (ℱ.le 0) _ hA0
    by_cases hP0 : P A = 0
    · rw [hP0, zero_mul]; exact measure_mono_null Set.inter_subset_left hP0
    · have h1 := hlawQ A hA0 hP0
      have h2 : (ProbabilityTheory.cond P A) (G t ⁻¹' Bset) = P (G t ⁻¹' Bset) := by
        have := congrArg (fun μ => μ Bset) h1
        simpa [Measure.map_apply hGm hBm] using this
      rw [ProbabilityTheory.cond_apply hAm] at h2
      calc P (A ∩ G t ⁻¹' Bset) = P A * ((P A)⁻¹ * P (A ∩ G t ⁻¹' Bset)) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hP0 (measure_ne_top _ _), one_mul]
        _ = P A * P (G t ⁻¹' Bset) := by rw [h2]
  have hmapL : ∀ L : H →L[ℝ] ℝ, (law P (G t)).map L =
      gaussianReal 0 (v ((InnerProductSpace.toDual ℝ H).symm L)).toNNReal := by
    intro L
    set y := (InnerProductSpace.toDual ℝ H).symm L with hy
    have hL : (L : H → ℝ) = fun z => inner ℝ y z := by
      funext z; rw [hy, InnerProductSpace.toDual_symm_apply]
    unfold law
    rw [Measure.map_map L.continuous.measurable hGm]
    have : (⇑L ∘ G t) = fun ω => inner ℝ y (G t ω) := by funext ω; simp [hL]
    rw [this]; exact hmargP y
  have hgauss : IsGaussian (law P (G t)) := isGaussian_of_map_eq_gaussianReal fun L => ⟨0, _, hmapL L⟩
  have hcent : ∀ L : StrongDual ℝ H, ∫ z, L z ∂(law P (G t)) = 0 := by
    intro L
    have h1 : ∫ z, L z ∂(law P (G t)) = ∫ w, w ∂((law P (G t)).map L) :=
      (integral_map L.continuous.measurable.aemeasurable aestronglyMeasurable_id).symm
    rw [h1, hmapL L]; exact integral_id_gaussianReal
  have hcg : IsCenteredGaussian (law P (G t)) := ⟨hgauss, hcent⟩
  refine ⟨hindep, hcg, ?_⟩
  haveI := hgauss
  have hmemLp := IsGaussian.memLp_id (law P (G t)) 2 (by norm_num)
  have hmean := gaussian_mean_zero hcg
  have hL2 : ∀ z : H, MemLp (fun ω => inner ℝ z (G t ω)) 2 P := fun z => by
    have h1 := IsGaussian.memLp_dual (law P (G t)) (innerSL ℝ z) 2 (by norm_num)
    have h2 : MemLp (fun w => innerSL ℝ z w) 2 (P.map (G t)) := h1
    exact (memLp_map_measure_iff (innerSL ℝ z).continuous.aestronglyMeasurable
      hGm.aemeasurable).1 h2
  have hcov : ∀ x y, covarianceBilin (law P (G t)) x y =
      ∫ ω, inner ℝ x (G t ω) * inner ℝ y (G t ω) ∂P := by
    intro x y
    rw [covarianceBilin_apply hmemLp]
    have h0 : ∫ z : H, (id z) ∂(law P (G t)) = 0 := hmean
    rw [h0]
    simp only [sub_zero, id]
    unfold law
    exact integral_map hGm.aemeasurable (((measurable_const.inner measurable_id).mul
      (measurable_const.inner measurable_id)).aestronglyMeasurable)
  have hsq : ∀ z, ∫ ω, inner ℝ z (G t ω) ^ 2 ∂P = v z := by
    intro z
    have hm1 : Measurable (fun z' : H => inner ℝ z z') := measurable_const.inner measurable_id
    have h1 : ∫ ω, inner ℝ z (G t ω) ^ 2 ∂P =
        ∫ w, w ^ 2 ∂(P.map (fun ω => inner ℝ z (G t ω))) := by
      have hm2 : AEStronglyMeasurable (fun w : ℝ => w ^ 2)
          (P.map (fun ω => inner ℝ z (G t ω))) := (measurable_id.pow_const 2).aestronglyMeasurable
      exact (integral_map (f := fun w : ℝ => w ^ 2) (hm1.comp hGm).aemeasurable hm2).symm
    rw [h1, hmargP z]
    unfold gaussianLaw
    rw [integral_sq_gaussianReal_zero, Real.coe_toNNReal _ (hv0 z)]
  intro x y
  rw [hcov]
  have hxy : ∫ ω, inner ℝ x (G t ω) * inner ℝ y (G t ω) ∂P = (v (x + y) - v x - v y) / 2 := by
    have hI : ∀ z, Integrable (fun ω => inner ℝ z (G t ω) ^ 2) P := fun z => (hL2 z).integrable_sq
    have hprod : Integrable (fun ω => inner ℝ x (G t ω) * inner ℝ y (G t ω)) P :=
      (hL2 x).integrable_mul (hL2 y)
    have e1 : ∀ ω, inner ℝ (x + y) (G t ω) ^ 2 = inner ℝ x (G t ω) ^ 2 +
        2 * (inner ℝ x (G t ω) * inner ℝ y (G t ω)) + inner ℝ y (G t ω) ^ 2 := by
      intro ω; rw [inner_add_left]; ring
    have h3 := hsq (x + y)
    simp_rw [e1] at h3
    have hIx : Integrable (fun ω => inner ℝ x (G t ω) ^ 2) P := hI x
    have hIy : Integrable (fun ω => inner ℝ y (G t ω) ^ 2) P := hI y
    have hB' : Integrable (fun ω => 2 * (inner ℝ x (G t ω) * inner ℝ y (G t ω))) P :=
      hprod.const_mul 2
    have hAB : Integrable (fun ω => inner ℝ x (G t ω) ^ 2 +
        2 * (inner ℝ x (G t ω) * inner ℝ y (G t ω))) P := hIx.add hB'
    rw [integral_add hAB hIy, integral_add hIx hB', integral_const_mul, hsq x, hsq y] at h3
    linarith
  have hR : ∫ r in Set.Icc 0 t, inner ℝ (Sb r x) (Sb r y) = (v (x + y) - v x - v y) / 2 := by
    simp only [hv, hD.v_eq]
    have e2 : ∀ r, inner ℝ (Sb r x) (Sb r y) =
        (‖Sb r (x + y)‖ ^ 2 - ‖Sb r x‖ ^ 2 - ‖Sb r y‖ ^ 2) / 2 := by
      intro r; rw [map_add, norm_add_sq_real]; ring
    simp_rw [e2]
    have h1 : IntegrableOn (fun r => ‖Sb r (x + y)‖ ^ 2) (Set.Icc 0 t) := hD.norm_sq_int _
    have h2 : IntegrableOn (fun r => ‖Sb r x‖ ^ 2) (Set.Icc 0 t) := hD.norm_sq_int _
    have h3 : IntegrableOn (fun r => ‖Sb r y‖ ^ 2) (Set.Icc 0 t) := hD.norm_sq_int _
    have h12 : IntegrableOn (fun r => ‖Sb r (x + y)‖ ^ 2 - ‖Sb r x‖ ^ 2) (Set.Icc 0 t) := h1.sub h2
    rw [integral_div, integral_sub h12 h3, integral_sub h1 h2]
  rw [hxy, hR]

end PC9

section PC10
open Classical HilbertCLTAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]
variable {e : HilbertBasis ι ℝ H} {t : ℝ} {Sb : ℝ → H →L[ℝ] H} {T : ℝ → ℝ}

lemma pc_enorm_sq_vec (v : H) : ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

lemma pc_enorm_sq_tsum (e : HilbertBasis ι ℝ H) (v : H) :
    ‖v‖ₑ ^ 2 = ∑' i, ‖inner ℝ v (e i)‖ₑ ^ 2 := by
  rw [enorm_tsum_sq_of_hasSum (hasSum_inner_sq e v), pc_enorm_sq_vec]

/-- The pair family `D(r, ω, (i,j)) = 1_{r ≤ t} ⟨(S'_r - Sb_r) e_j, e_i⟩`. -/
def pcDfam (e : HilbertBasis ι ℝ H) (t : ℝ) (S' : ℝ → Ω → H →L[ℝ] H) (Sb : ℝ → H →L[ℝ] H) :
    ℝ → Ω → ι × ι → ℝ :=
  fun r ω p => if r ≤ t then inner ℝ ((S' r ω - Sb r) (e p.2)) (e p.1) else 0

theorem pc_L2_bound (hD : PCDetData e t Sb T) {B : ℝ≥0 → Ω → ι → ℝ}
    (hB : IsCylindricalBrownian P ℱ B) (ht : 0 ≤ t)
    (S' : ℝ → Ω → H →L[ℝ] H)
    (hSprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S' r ω x) y))
    (hfS : ∀ x, IsCtbl P ℱ (fun r ω j => if r ≤ t then inner ℝ (S' r ω (e j)) x else 0))
    {Z : H → ℝ → Ω → ℝ}
    (hZ : ∀ x, IsItoC P ℱ B (fun r ω j => if r ≤ t then inner ℝ (S' r ω (e j)) x else 0) (Z x))
    {G : ℝ → Ω → H}
    (hG : ∀ x : H, ∃ J : ℝ → Ω → ℝ, IsItoC P ℱ B (fSb e t Sb x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (G τ ω) x) =ᵐ[P] J τ)
    (hGm : Measurable (G t)) {M' : Ω → H} (hM'm : Measurable M')
    (hMZ : ∀ x, (fun ω => inner ℝ (M' ω) x) =ᵐ[P] Z x t)
    (dd : ℝ → Ω → ℝ)
    (hdd : ∀ r ∈ Set.Icc 0 t, ∀ ω, Summable (fun j => ‖(S' r ω - Sb r) (e j)‖ ^ 2) ∧
      ∑' j, ‖(S' r ω - Sb r) (e j)‖ ^ 2 ≤ dd r ω) :
    ∫⁻ ω, ‖M' ω - G t ω‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (dd r ω)) ∂P := by
  have hDfun : ∀ i : ι, (fun r ω (j : ι) => pcDfam e t S' Sb r ω (i, j)) =
      fun r ω (j : ι) => (if r ≤ t then inner ℝ (S' r ω (e j)) (e i) else 0) -
        fSb e t Sb (e i) r ω j := by
    intro i; funext r ω j
    by_cases hr : r ≤ t <;> simp [pcDfam, fSb, hr, inner_sub_left]
  -- the per-coordinate bound
  have hcoord : ∀ i : ι, ∫⁻ ω, ‖inner ℝ (M' ω - G t ω) (e i)‖ₑ ^ 2 ∂P ≤
      ∑' j, cT P (fun r ω (j : ι) => pcDfam e t S' Sb r ω (i, j)) j t := by
    intro i
    obtain ⟨J, hJ, hae⟩ := hG (e i)
    have hdiff := IsItoC.sub hB (hfS (e i)) (hD.ctbl (Ω := Ω) (ℱ := ℱ) (e i)) (hZ (e i)) hJ
    have hΞd := pc_isCtbl_sub (hfS (e i)) (hD.ctbl (Ω := Ω) (ℱ := ℱ) (e i))
    have h1 := hdiff.lintegral_sq_le hΞd hB ht
    rw [← hDfun i] at h1
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr_ae ?_
    filter_upwards [hMZ (e i), hae t ht] with ω h1 h2
    rw [inner_sub_left, h1, h2]
  have hprog : ∀ p : ι × ι, IsProgressive ℱ (fun r ω => pcDfam e t S' Sb r ω p) := by
    intro p
    have h1 : IsProgressive ℱ (fun r ω => inner ℝ (S' r ω (e p.2)) (e p.1)) := hSprog _ _
    have h2 : IsProgressive ℱ (fun r (_ : Ω) => inner ℝ (Sb r (e p.2)) (e p.1)) :=
      pc_isProgressive_det ((hD.meas _).inner measurable_const)
    have h3 : IsProgressive ℱ (fun r ω => inner ℝ (S' r ω (e p.2)) (e p.1) -
        inner ℝ (Sb r (e p.2)) (e p.1)) := fun i => (h1 i).sub (h2 i)
    have h4 := pc_isProgressive_ite (β := ℝ) h3 (measurableSet_Iic (a := t))
    convert h4 using 3 with r ω
    simp [pcDfam, inner_sub_left]
  calc ∫⁻ ω, ‖M' ω - G t ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, ∑' i, ‖inner ℝ (M' ω - G t ω) (e i)‖ₑ ^ 2 ∂P :=
        lintegral_congr fun ω => pc_enorm_sq_tsum e _
    _ = ∑' i, ∫⁻ ω, ‖inner ℝ (M' ω - G t ω) (e i)‖ₑ ^ 2 ∂P := by
        rw [lintegral_tsum]
        intro i
        exact (((hM'm.sub hGm).inner measurable_const).enorm.pow_const 2).aemeasurable
    _ ≤ ∑' i, ∑' j, cT P (fun r ω (j : ι) => pcDfam e t S' Sb r ω (i, j)) j t :=
        ENNReal.tsum_le_tsum hcoord
    _ = ∑' p : ι × ι, cT P (pcDfam e t S' Sb) p t := by
        exact (ENNReal.tsum_prod (f := fun i j => cT P (pcDfam e t S' Sb) (i, j) t)).symm
    _ = ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑' p, ‖pcDfam e t S' Sb r ω p‖ₑ ^ 2) ∂P := pc_tsum_cT hprog t
    _ ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (dd r ω)) ∂P := by
        refine lintegral_mono fun ω => setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        obtain ⟨hsum, hle⟩ := hdd r hr ω
        have hrt : r ≤ t := hr.2
        have : ∀ p : ι × ι, pcDfam e t S' Sb r ω p = inner ℝ ((S' r ω - Sb r) (e p.2)) (e p.1) := by
          intro p; simp [pcDfam, hrt]
        simp_rw [this]
        have hp : ∑' p : ι × ι, ‖inner ℝ ((S' r ω - Sb r) (e p.2)) (e p.1)‖ₑ ^ 2 =
            ∑' i, ∑' j, ‖inner ℝ ((S' r ω - Sb r) (e j)) (e i)‖ₑ ^ 2 :=
          ENNReal.tsum_prod (f := fun i j => ‖inner ℝ ((S' r ω - Sb r) (e j)) (e i)‖ₑ ^ 2)
        rw [hp, ENNReal.tsum_comm]
        calc ∑' j, ∑' i, ‖inner ℝ ((S' r ω - Sb r) (e j)) (e i)‖ₑ ^ 2
            = ∑' j, ‖(S' r ω - Sb r) (e j)‖ₑ ^ 2 :=
              tsum_congr fun j => (pc_enorm_sq_tsum e _).symm
          _ = ∑' j, ENNReal.ofReal (‖(S' r ω - Sb r) (e j)‖ ^ 2) :=
              tsum_congr fun j => pc_enorm_sq_vec _
          _ = ENNReal.ofReal (∑' j, ‖(S' r ω - Sb r) (e j)‖ ^ 2) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) hsum).symm
          _ ≤ ENNReal.ofReal (dd r ω) := ENNReal.ofReal_le_ofReal hle

end PC10

section PC11
open Classical HilbertCLTAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma traceNormForm_le_basis_trace {ι : Type*} {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : IsTraceClassCov C)
    (e : HilbertBasis ι ℝ H) : traceNormForm C ≤ ∑' i, C (e i) (e i) := by
  obtain ⟨ℓ, hs, hℓ⟩ := hC.exists_decomp'
  have hd : ∀ x, C x x = ∑' j, inner ℝ (ℓ j) x ^ 2 := fun x => by
    rw [← (hℓ x x).tsum_eq]; exact tsum_congr fun j => (sq _).symm
  have h1 : ∑' i, C (e i) (e i) = ∑' j, ‖ℓ j‖ ^ 2 := by
    rw [← (hasSum_diag_decomp hs e).tsum_eq]
    exact tsum_congr fun i => hd (e i)
  refine Real.iSup_le (fun p => ?_) (tsum_nonneg fun i => hC.nonneg _)
  rw [h1]
  exact sum_abs_le_of_decomp hs hℓ _ _ p.2.1 p.2.2

lemma traceNormForm_hsCov_le {κ : Type*} [Countable κ] {Φ : κ → H}
    (hΦ : Summable fun k => ‖Φ k‖ ^ 2) : traceNormForm (hsCovForm Φ) ≤ ∑' k, ‖Φ k‖ ^ 2 := by
  obtain ⟨ι₀, -, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  refine (traceNormForm_le_basis_trace (isTraceClassCov_hsCovForm hΦ) b).trans (le_of_eq ?_)
  rw [← (hasSum_diag_decomp hΦ b).tsum_eq]
  refine tsum_congr fun i => ?_
  rw [hsCovForm_apply hΦ]
  exact tsum_congr fun k => (sq _).symm

end PC11

section PC11b
open Classical HilbertCLTAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ]

lemma pc_enorm_sq_vec' (v : H) : ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

lemma pc_meas_covDisc {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (t : ℝ)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    Measurable (fun p : ℝ × Ω => traceNormForm (hsCovForm (Φ (min p.1 t) p.2) - sb p.1)) := by
  refine measurable_traceNormForm (D := fun p : ℝ × Ω => hsCovForm (Φ (min p.1 t) p.2) - sb p.1)
    (fun x y => ?_)
  simp only [ContinuousLinearMap.sub_apply]
  have e1 : (fun p : ℝ × Ω => hsCovForm (Φ (min p.1 t) p.2) x y) = fun p : ℝ × Ω =>
      ∑' k, inner ℝ (Φ (min p.1 t) p.2 k) x * inner ℝ (Φ (min p.1 t) p.2 k) y := by
    funext p; exact hsCovForm_apply ((hΦ t).summable _ _) x y
  have e2 : Measurable (fun p : ℝ × Ω => hsCovForm (Φ (min p.1 t) p.2) x y) := by
    rw [e1]
    exact Measurable.tsum fun k => (((measurable_clamp ((hΦ t).prog k) t).inner measurable_const).mul
      ((measurable_clamp ((hΦ t).prog k) t).inner measurable_const))
  exact e2.sub ((hsb.meas x y).comp measurable_fst)

theorem pc_lintegral_covDisc {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) {t : ℝ}
    (ht : 0 ≤ t) (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal
        (traceNormForm (hsCovForm (Φ r ω) - sb r))) ∂P =
      ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb) := by
  set d : ℝ → Ω → ℝ := fun r ω => traceNormForm (hsCovForm (Φ r ω) - sb r) with hd
  set dc : ℝ × Ω → ℝ := fun p => traceNormForm (hsCovForm (Φ (min p.1 t) p.2) - sb p.1) with hdc
  have hdcm : Measurable dc := pc_meas_covDisc hΦ t sb hsb
  have hdc_eq : ∀ r ∈ Set.Icc 0 t, ∀ ω, dc (r, ω) = d r ω := fun r hr ω => by
    simp only [hdc, hd, min_eq_left hr.2]
  have hd0 : ∀ r ω, 0 ≤ d r ω := fun r ω => traceNormForm_nonneg _
  -- measurability of the sections
  have hsm : ∀ ω, Measurable fun r => dc (r, ω) := fun ω => hdcm.comp measurable_prodMk_right
  -- trace of the covariation
  set tr : ℝ → ℝ := fun r => traceNormForm (sb r) with htr
  have htrm : Measurable tr := measurable_traceNormForm (α := ℝ) sb hsb.meas
  have hbound : ∀ r ∈ Set.Icc 0 t, ∀ ω, d r ω ≤ (∑' k, ‖Φ r ω k‖ ^ 2) + tr r := by
    intro r hr ω
    have h1 := traceNormForm_sub_le (isTraceClassCov_hsCovForm ((hΦ t).summable r ω))
      (hsb.traceClass r hr)
    have h2 := traceNormForm_hsCov_le ((hΦ t).summable r ω)
    simp only [hd, htr]
    linarith
  -- finiteness of the double lintegral
  have hL : ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (d r ω)) ∂P < ⊤ := by
    have hA : ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (∑' k, ‖Φ r ω k‖ ^ 2)) ∂P < ⊤ := by
      have : ∀ r ω, ENNReal.ofReal (∑' k, ‖Φ r ω k‖ ^ 2) = ∑' k, ‖Φ r ω k‖ₑ ^ 2 := fun r ω => by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) ((hΦ t).summable r ω)]
        exact tsum_congr fun k => (pc_enorm_sq_vec' _).symm
      simp_rw [this]
      exact (hΦ t).sq
    have hB : ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (tr r) < ⊤ := hsb.int.lintegral_lt_top
    calc ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (d r ω)) ∂P
        ≤ ∫⁻ ω, ((∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (∑' k, ‖Φ r ω k‖ ^ 2)) +
            ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (tr r)) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [← lintegral_add_right _ (htrm.ennreal_ofReal)]
          refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
          refine (ENNReal.ofReal_le_ofReal (hbound r hr ω)).trans ?_
          exact ENNReal.ofReal_add_le
      _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hA, hB⟩
  set F : Ω → ℝ := fun ω => ∫ r in Set.Icc 0 t, d r ω with hF
  have hFeq : ∀ ω, F ω = ∫ r in Set.Icc 0 t, dc (r, ω) := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => (hdc_eq r hr ω).symm
  have hFm : StronglyMeasurable F := by
    have h1 : StronglyMeasurable fun ω => ∫ r in Set.Icc 0 t, dc (r, ω) :=
      (hdcm.comp (measurable_swap (α := Ω) (β := ℝ))).stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Set.Icc 0 t))
    have : F = fun ω => ∫ r in Set.Icc 0 t, dc (r, ω) := funext hFeq
    rw [this]; exact h1
  set Lr : Ω → ℝ≥0∞ := fun ω => ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (d r ω) with hLr
  have hLrm : Measurable Lr := by
    have h1 : Measurable fun ω => ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (dc (r, ω)) :=
      (hdcm.ennreal_ofReal.comp (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right'
        (ν := volume.restrict (Set.Icc 0 t))
    have : Lr = fun ω => ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (dc (r, ω)) := by
      funext ω
      exact setLIntegral_congr_fun measurableSet_Icc fun r hr => by rw [hdc_eq r hr ω]
    rw [this]; exact h1
  have hae : ∀ᵐ ω ∂P, Lr ω < ⊤ := ae_lt_top hLrm hL.ne
  have hint : ∀ ω, Lr ω < ⊤ → IntegrableOn (fun r => d r ω) (Set.Icc 0 t) := fun ω hω => by
    refine ⟨((hsm ω).aestronglyMeasurable).congr
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hdc_eq r hr ω)), ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_of_nonneg (hd0 _ ω)]
    exact hω
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => setIntegral_nonneg measurableSet_Icc fun r _ => hd0 r ω
  have hFL : ∀ᵐ ω ∂P, ENNReal.ofReal (F ω) = Lr ω := by
    filter_upwards [hae] with ω hω
    exact ofReal_integral_eq_lintegral_ofReal (hint ω hω) (Eventually.of_forall fun r => hd0 r ω)
  have hFint : Integrable F P := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ ω, ‖F ω‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (F ω) ∂P :=
          lintegral_congr fun ω => by rw [Real.enorm_of_nonneg (hF0 ω)]
      _ = ∫⁻ ω, Lr ω ∂P := lintegral_congr_ae hFL
      _ < ⊤ := hL
  show ∫⁻ ω, Lr ω ∂P = ENNReal.ofReal (∫ ω, F ω ∂P)
  rw [ofReal_integral_eq_lintegral_ofReal hFint (Eventually.of_forall hF0)]
  exact (lintegral_congr_ae hFL).symm

end PC11b

section PC12
open Classical HilbertCLTAux

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {κ : Type*} [Countable κ] {ι : Type*} [Countable ι]

lemma pc_isCtbl_of_HS {A : Type*} [Countable A] {ξ : ℝ → Ω → A → ℝ} {Φ : ℝ → Ω → κ → H}
    (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H)
    (hprog : ∀ a, IsProgressive ℱ (fun r ω => ξ r ω a))
    (hle : ∀ r ω, ∑' a, ‖ξ r ω a‖ₑ ^ 2 ≤ (∑' k, ‖Φ r ω k‖ₑ ^ 2) * ‖x‖ₑ ^ 2) : IsCtbl P ℱ ξ :=
  pc_isCtbl_of_le hprog (g := fun r ω => (∑' k, ‖Φ r ω k‖ₑ ^ 2) * ‖x‖ₑ ^ 2) hle (fun T => by
    have h1 : ∫⁻ ω, (∫⁻ r in Set.Icc 0 T, (∑' k, ‖Φ r ω k‖ₑ ^ 2) * ‖x‖ₑ ^ 2) ∂P =
        hsSqIntegralOn P Φ T * ‖x‖ₑ ^ 2 := by
      unfold hsSqIntegralOn
      rw [← lintegral_mul_const' _ _ (pc_enorm_sq_ne_top x)]
      refine lintegral_congr fun ω => ?_
      rw [lintegral_mul_const' _ _ (pc_enorm_sq_ne_top x)]
    rw [h1]
    exact (ENNReal.mul_lt_top (hΦ T).sq (lt_top_iff_ne_top.2 (pc_enorm_sq_ne_top x))).ne)

lemma pc_ctbl_S {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (e : HilbertBasis ι ℝ H)
    {S : ℝ → Ω → H →L[ℝ] H}
    (hSsq : ∀ r ω, IsSqrtOfForm (S r ω) (hsCovForm (Φ r ω)))
    (hSprog : ∀ x y, IsProgressive ℱ (fun r ω => inner ℝ (S r ω x) y)) (t : ℝ) (x : H)
    (hpar : ∀ r ω x, HasSum (fun j => inner ℝ (S r ω (e j)) x ^ 2) (‖S r ω x‖ ^ 2)) :
    IsCtbl P ℱ (fun r ω (j : ι) => if r ≤ t then inner ℝ (S r ω (e j)) x else 0) := by
  refine pc_isCtbl_of_HS hΦ x (fun j => ?_) (fun r ω => ?_)
  · have := pc_isProgressive_ite (β := ℝ) (hSprog (e j) x) (measurableSet_Iic (a := t))
    simpa using this
  · by_cases hr : r ≤ t
    · simp only [hr, ite_true]
      rw [enorm_tsum_sq_of_hasSum (hpar r ω x)]
      have h1 : ‖S r ω x‖ ^ 2 ≤ (∑' k, ‖Φ r ω k‖ ^ 2) * ‖x‖ ^ 2 := by
        have := (hSsq r ω).sq x x
        rw [real_inner_self_eq_norm_sq] at this
        rw [this]
        exact hsCovForm_le' ((hΦ 0).summable r ω) x
      calc ENNReal.ofReal (‖S r ω x‖ ^ 2) ≤ ENNReal.ofReal ((∑' k, ‖Φ r ω k‖ ^ 2) * ‖x‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal h1
        _ = (∑' k, ‖Φ r ω k‖ₑ ^ 2) * ‖x‖ₑ ^ 2 := by
            rw [ENNReal.ofReal_mul (tsum_nonneg fun k => sq_nonneg _),
              ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) ((hΦ 0).summable r ω),
              pc_enorm_sq_vec' x]
            congr 1
            exact tsum_congr fun k => (pc_enorm_sq_vec' _).symm
    · simp [hr]

lemma pc_ctbl_pcXi {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (x : H) (t : ℝ) :
    IsCtbl P ℱ (pcXi t Φ x ι) := by
  refine pc_isCtbl_of_HS hΦ x (fun a => ?_) (fun r ω => ?_)
  · rcases a with k | l
    · have h0 : IsProgressive ℱ (fun r ω => inner ℝ (Φ r ω k) x) :=
        fun i => ((hΦ 0).prog k i).inner measurable_const
      have := pc_isProgressive_ite (β := ℝ) h0 (measurableSet_Iic (a := t))
      simpa [pcXi] using this
    · simpa [pcXi] using isProgressive_const ℱ (0 : ℝ)
  · rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
    have h2 : ∑' l : ι, ‖(pcXi t Φ x ι r ω) (Sum.inr l)‖ₑ ^ 2 = 0 := by
      simp [pcXi]
    rw [h2, add_zero, ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun k => ?_
    by_cases hr : r ≤ t
    · simp only [pcXi, Sum.elim_inl, hr, ite_true]
      exact pc_enorm_inner_sq_le _ _
    · simp [pcXi, hr]

lemma pc_meas_Lr {Φ : ℝ → Ω → κ → H} (hΦ : ∀ T, IsHSIntegrand P ℱ T Φ) (t : ℝ)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    Measurable (fun ω => ∫⁻ r in Set.Icc 0 t,
      ENNReal.ofReal (traceNormForm (hsCovForm (Φ r ω) - sb r))) := by
  have hdcm := pc_meas_covDisc hΦ t sb hsb
  have h1 : Measurable fun ω => ∫⁻ r in Set.Icc 0 t,
      ENNReal.ofReal (traceNormForm (hsCovForm (Φ (min r t) ω) - sb r)) :=
    (hdcm.ennreal_ofReal.comp (measurable_swap (α := Ω) (β := ℝ))).lintegral_prod_right'
      (ν := volume.restrict (Set.Icc 0 t))
  have : (fun ω => ∫⁻ r in Set.Icc 0 t, ENNReal.ofReal (traceNormForm (hsCovForm (Φ r ω) - sb r))) =
      fun ω => ∫⁻ r in Set.Icc 0 t,
        ENNReal.ofReal (traceNormForm (hsCovForm (Φ (min r t) ω) - sb r)) := by
    funext ω
    exact setLIntegral_congr_fun measurableSet_Icc fun r hr => by rw [min_eq_left hr.2]
  rw [this]; exact h1

lemma pc_detData (e : HilbertBasis ι ℝ H) (t : ℝ) (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ))
    (hsb : IsDetCovDensity t sb) {Sb : ℝ → H →L[ℝ] H} (hSbm : OpMeas Sb)
    (hSb0 : ∀ r, r ∉ Set.Icc 0 t → Sb r = 0) (hSb : ∀ r ∈ Set.Icc 0 t, IsSqrtOfForm (Sb r) (sb r)) :
    ∃ T : ℝ → ℝ, PCDetData e t Sb T := by
  set T : ℝ → ℝ := (Set.Icc 0 t).indicator (fun r => ∑' i, sb r (e i) (e i)) with hT
  have hTm : Measurable T :=
    (Measurable.tsum fun i => hsb.meas (e i) (e i)).indicator measurableSet_Icc
  refine ⟨T, ⟨hSbm, hSb0, ?_, ?_, ?_, hTm, ?_, ?_⟩⟩
  · intro r x
    by_cases hr : r ∈ Set.Icc 0 t
    · have := hasSum_inner_sq e (Sb r x)
      convert this using 2 with j
      rw [(hSb r hr).symm (e j) x, real_inner_comm]
    · simp [hSb0 r hr]
  · intro r hr x
    obtain ⟨T0, hT0, hb⟩ := (hsb.traceClass r hr).hasSum_basis e
    have h1 : ‖Sb r x‖ ^ 2 = sb r x x := by
      rw [← real_inner_self_eq_norm_sq, (hSb r hr).sq]
    simp only [hT, Set.indicator_of_mem hr, hT0.tsum_eq]
    rw [h1]; exact hb x
  · intro r hr
    obtain ⟨T0, hT0, hb⟩ := (hsb.traceClass r hr).hasSum_basis e
    simp only [hT, Set.indicator_of_mem hr, hT0.tsum_eq]
    convert hT0 using 2 with i
    rw [← real_inner_self_eq_norm_sq, (hSb r hr).sq]
  · intro r hr
    simp only [hT, Set.indicator_of_mem hr]
    exact tsum_nonneg fun i => (hsb.traceClass r hr).nonneg _
  · refine hsb.int.mono' hTm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
    have h0 : 0 ≤ T r := by
      simp only [hT, Set.indicator_of_mem hr]
      exact tsum_nonneg fun i => (hsb.traceClass r hr).nonneg _
    rw [Real.norm_of_nonneg h0]
    simp only [hT, Set.indicator_of_mem hr]
    exact (hsb.traceClass r hr).tsum_basis_le e

end PC12


/-! ### Corollary A.23: predictable polar coupling in Hilbert space -/

section Polar

universe uΩ

variable {Ω : Type uΩ} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

set_option warn.classDefReducibility false in
/-- The σ-algebra generated by a family of real processes (used for "independent of `𝒢`"). -/
def cylindricalPathSigma {κ : Type*} (B : ℝ≥0 → Ω → κ → ℝ) : MeasurableSpace Ω :=
  ⨆ (τ : ℝ≥0) (k : κ), MeasurableSpace.comap (fun ω => B τ ω k) inferInstance

/- CLT-02c attempt 2, universe finding (NOT fixed here; statements are frozen).
`hilbert_polar_coupling` is FALSE as typed for `Ω : Type u` with `u ≥ 1`, because its enlargement is
`Ω' : Type` (and `ι : Type`) while `Ω` is universe polymorphic (`variable {Ω : Type*}`).
Counterexample sketch: take `Ω = Ω₀ × (Cardinal.{0} → Bool)` (a `Type 1`), `P` = (any admissible
data on `Ω₀`, e.g. `Φ = 0`, `M = 0`) times the fair-coin product measure.  `MeasurePreserving π P' P`
with `Ω' : Type` would give `|Cardinal.{0}|` many sets `π⁻¹{ω | ω i = true} ⊆ Ω'`, pairwise at
`P'`-distance `1/2`, hence pairwise distinct, i.e. an injection `Cardinal.{0} ↪ Set Ω'` into a
`Type`-sized type, which is impossible.  Same repair as `dds_coupling_conditional`: put `Ω'` (and
`ι`) in `Type u_1` (enlargement `Ω × Ω''` is then in the same universe, so the intended
construction below goes through).  `hilbert_martingale_w2` is true as typed, but its route needs a
coupling space in `Type u_1`, hence the repaired `hilbert_polar_coupling`. -/

/- CLT-02c attempt 3, second finding (statement of `hilbert_polar_coupling` is FALSE as typed, NOT fixed
here; statements are frozen).  The conjunct `∀ r, IsSqrtOfForm (Sb r) (sb r)` quantifies over ALL
`r : ℝ`, but `IsDetCovDensity t sb` constrains `sb σ` only for `σ ∈ Icc 0 t` (trace class there);
`IsSqrtOfForm.sq` gives `sb r x x = ‖Sb r x‖² ≥ 0`.  Counterexample (checked in Lean, derives `False`
from the statement): `Ω = PUnit`, `P = dirac`, `ℱ` constant, `κ = Empty`, `Φ = 0`, `M = 0`, `H = ℝ`,
`t = 0`, `sb σ = 0` for `σ ≤ 0` and `sb σ x y = -(x*y)` for `σ > 0`: all hypotheses hold, but
`(hSb 1).sq 1 1` says `0 ≤ ⟪Sb 1 1, Sb 1 1⟫ = sb 1 1 1 = -1`.
Third (soft) defect, same origin: `IsHSIntegrand` bounds `Φ` in `L²` only on `[0,t]` while
`IsHilbertItoIntegral` (hypothesis `hM` and the two conclusions on `S`, `Sb`) has the `approx` field for
ALL `τ ≥ 0`; for `τ > t`, `itoIntegral` of an integrand that is not `L²` on `[0,τ]` is an arbitrary
`Classical.choose` (`IsItoIntegral.approx` is vacuous there), so those conclusions are not provable.
Suggested repair: `∀ r ∈ Set.Icc 0 t, IsSqrtOfForm (Sb r) (sb r)` (and for `S`), and the two
`IsHilbertItoIntegral` conclusions only for integrands/times in `[0,t]` (e.g. `approx` for
`τ ∈ Icc 0 t`, or integrands killed after `t`).  `hilbert_martingale_w2` below uses only the last five
conjuncts (law of `G t`, its covariance, the `L²` bound) and `MeasurePreserving π`, so its proof is
unchanged by any such repair. -/

/- CLT-02c attempt 4, third finding (the statements of `hilbert_polar_coupling` AND of
`hilbert_martingale_w2` are FALSE as typed; NOT fixed here, statements are frozen).
The defect of attempt 3 (hypothesis `IsHSIntegrand P ℱ t Φ` controls `Φ` only on `[0,t]`, while
`IsHilbertItoIntegral.approx` is over all `τ ≥ 0`) is fatal on the HYPOTHESIS side too: `itoIntegral` is
`if h : ∃ M, IsItoIntegral … then h.choose else 0`, so when the unkilled integrals have no continuous
version, `itoIntegral = 0` and `hM` holds for `M = 0`.  Counterexample: `Ω` the Wiener space of a one
dimensional Brownian motion `W` with its natural filtration, `κ = Unit`, `H = ℝ`, `t > 0`, and the
deterministic progressive `Φ r ω () = 1` for `r ≤ t`, `(t+1-r)^{-1/2}` for `t < r < t+1`, `0` for
`r ≥ t+1` (so `hΦ` holds: `L²` on `[0,t]`).  For `t < t' < t+1`, `Φ` is `L²` on `[0,t']`, so
`IsItoIntegral.approx` pins `M_{t'}` to the true integral `N_{t'}`, whose quadratic variation
`∫_0^{t'}Φ² ↑ ∞` as `t' ↑ t+1`; hence `limsup N = ∞` a.s. and no `M` with `cont` (for every `ω`) exists,
so `¬∃ M, IsItoIntegral` and `M := 0` satisfies `hM`.  Then the 5th conjunct of the conclusion fails:
`S_r = 1` on `[0,t]` is forced (the unique nonnegative square root of `Σ_r = 1`), so for `τ = t`,
`x = 1` the integral of the killed integrand against `B` has second moment `t > 0` (Itô isometry) but
must be `L²`-close to `⟨M_t,1⟩ = 0`.  Likewise `hilbert_martingale_w2` fails with `sb ≡ 2`,
`γ = N(0,2t)`: `W₂²(δ₀,γ) = 2t > t = covDiscrepancy`.
Suggested repair (as for `hilbert_direct_sum_ito`, docs/ISSUES.md): `hΦ : ∀ T, IsHSIntegrand P ℱ T Φ` (`L²`
on every finite horizon) in both theorems; then every coordinate integrand is `IsProgressiveL2`, the
`itoIntegral` of `hM` is the genuine integral, and the route of the docstring below goes through; the
integrand of `hM` (unkilled) is compared with the killed integrand of the 5th conjunct by the block
property `itoIntegral_blockInt`.  (Alternatively: `hM` for the integrand killed after `t`.)  The helper block
above (`FragP1`-`FragR12`) contains the bulk of the construction for either repair. -/

/-- Corollary A.23 `M:B:lem:hilbert-martingale-w2` (source lines 10629-10654).  Let `𝒢 ⊂ ℱ_0`,
`W` a `U`-cylindrical Brownian motion, `Φ` a Hilbert–Schmidt integrand with
`E ∫_0^t ‖Φ_r‖²_{𝓛₂} < ∞`, `M = ∫Φ dW`, `Σ_r = Φ_rΦ_r^*`, and `Σ̄ : [0,t] → 𝔖₁⁺(H)`
deterministic, measurable, with `∫_0^t Tr Σ̄_r dr < ∞`.  Then on an enlargement of the filtered
probability space (`Ω'`, `π`, `ℱ'`) there is an `H`-cylindrical Brownian motion `B` (indexed by a
Hilbert basis `e` of `H`), Brownian with respect to the enlarged filtration and independent of
`𝒢`, such that `M_τ = ∫_0^τ Σ_r^{1/2} dB_r` for `0 ≤ τ ≤ t` (`B:eq:polar-Brownian-representation`,
with `Σ_r^{1/2}` characterised by `IsSqrtOfForm`), and, for `G_τ := ∫_0^τ Σ̄_r^{1/2} dB_r`,
`G_t` is centered Gaussian, independent of `𝒢`, with covariance `∫_0^t Σ̄_r dr`, and
`E ‖M_t - G_t‖² ≤ E ∫_0^t ‖Σ_r - Σ̄_r‖_{𝔖₁} dr` (the coupling behind
`B:eq:hilbert-martingale-w2`, stated as the `lintegral` bound so that finiteness is asserted).

PLAN (source lines 10656-10668 and `U:lem:polar` of the whole-space supplement): polar
decomposition `Φ_r = Σ_r^{1/2} V_r` with `V_r : U → H` a partial isometry chosen measurably in `r,ω`
(Borel functional calculus / spectral decomposition of the compact nonnegative operator `Σ_r`,
rank-one decomposition as in `HilbertCLTAux.exists_rank_one_decomp`); set
`B := ∫ V dW + ∫ (I - V V^*) dW'` with `W'` an independent `H`-cylindrical Brownian motion on
`Ω' = Ω × Ω''` (`exists_enlargement` for each finite block, product measure, `generatedFiltration`),
which is an `H`-cylindrical Brownian motion by `levy_characterization`
(`HRS/Stochastic/DDS.lean`) applied to finite subfamilies, independent of `𝒢` since Brownian
with respect to a filtration containing `𝒢` at time `0`.  Then `∫Σ^{1/2} dB = ∫Φ dW` by
linearity (`itoIntegral_add`, `itoIntegral_smul`, `IsItoIntegral.ae_eq_forall`).  The `L²` bound is
the Itô isometry (`IsItoIntegral.lintegral_sub_sq` / `itoIntegral_isometry` coordinatewise) and the
Powers–Størmer inequality `‖Σ^{1/2} - Σ̄^{1/2}‖²_{𝔖₂} ≤ ‖Σ - Σ̄‖_{𝔖₁}` (external: Powers–Størmer,
Comm. Math. Phys. 16 (1970), Thm. 1; also Simon, *Trace ideals*, 2nd ed., Thm. 5.2 / Kittaneh,
for nonnegative trace-class operators). -/
theorem hilbert_polar_coupling (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (𝒢 : InitialSigma ℱ)
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → κ → H) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (M : ℝ → Ω → H) (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb) :
    ∃ (Ω' : Type uΩ) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (ι : Type uΩ) (_ : Countable ι) (e : HilbertBasis ι ℝ H) (B : ℝ≥0 → Ω' → ι → ℝ)
      (S : ℝ → Ω → (H →L[ℝ] H)) (Sb : ℝ → (H →L[ℝ] H)) (G : ℝ → Ω' → H),
      (∀ τ, (ℱ τ).comap π ≤ ℱ' τ) ∧
      IsCylindricalBrownian P' ℱ' B ∧
      Indep (𝒢.1.comap π) (cylindricalPathSigma B) P' ∧
      (∀ r ω, IsSqrtOfForm (S r ω) (hsCovForm (Φ r ω))) ∧
      IsHilbertItoIntegral P' ℱ' B (fun r ω' j => if r ≤ t then S r (π ω') (e j) else 0)
        (fun τ ω' => M (min τ t) (π ω')) ∧
      (∀ r ∈ Set.Icc 0 t, IsSqrtOfForm (Sb r) (sb r)) ∧
      IsHilbertItoIntegral P' ℱ' B (fun r _ j => if r ≤ t then Sb r (e j) else 0) G ∧
      AEMeasurable (G t) P' ∧
      Indep (𝒢.1.comap π) (MeasurableSpace.comap (G t) inferInstance) P' ∧
      IsCenteredGaussian (law P' (G t)) ∧
      (∀ x y, covarianceBilin (law P' (G t)) x y = ∫ σ in Set.Icc 0 t, sb σ x y) ∧
      ∫⁻ ω', ‖M t (π ω') - G t ω'‖ₑ ^ 2 ∂P' ≤
        ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb) := by
  classical
  obtain ⟨ι, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, uΩ} (H := H)
  obtain ⟨S, ψ, hSsq, hSprog, hψprog, hψo, hψe, hψn, hψt⟩ := exists_polar_family e Φ
    (fun k => (hΦ 0).prog k) (fun r ω => (hΦ 0).summable r ω)
  obtain ⟨Sb, hSbm, hSb0, hSb⟩ := exists_sqrt_density e t sb hsb
  obtain ⟨T, hD⟩ := pc_detData e t sb hsb hSbm hSb0 hSb
  have hW₂ : IsCylindricalBrownian (wMeasure ι) (wFiltration ι)
      (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  have h𝔚 : IsCylindricalBrownian (P.prod (wMeasure ι))
      (prodFiltration P (wMeasure ι) ℱ (wFiltration ι))
      (sumFam W (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i))) :=
    isCylindricalBrownian_prod hW hW₂
  set P' : Measure (Ω × (ι → WienerSeq)) := P.prod (wMeasure ι) with hP'
  set ℱ' := prodFiltration P (wMeasure ι) ℱ (wFiltration ι) with hℱ'
  set 𝔚 := sumFam W (fun t (ω : ι → WienerSeq) (i : ι) => wienerPath t (ω i)) with h𝔚def
  have hπp : MeasurePreserving (Prod.fst : Ω × (ι → WienerSeq) → Ω) P' P := measurePreserving_fst
  have hπm : ∀ s, Measurable[ℱ' s, ℱ s] (Prod.fst : Ω × (ι → WienerSeq) → Ω) := fun s =>
    Measurable.of_comap_le (le_sup_of_le_left le_sup_left)
  have h𝔚l : ∀ s (ω' : Ω × (ι → WienerSeq)) k, 𝔚 s ω' (Sum.inl k) = W s ω'.1 k :=
    fun _ _ _ => rfl
  set ψ' : ι → ℝ → Ω × (ι → WienerSeq) → κ ⊕ ι → ℝ := fun j r ω' a => ψ j r ω'.1 a with hψ'
  have hψctbl : ∀ j, IsCtbl P' ℱ' (ψ' j) := fun j =>
    pc_isCtbl_comp hπm hπp (pc_isCtbl_of_hasSum_one (hψprog j)
      (fun r ω => by simpa [sq] using hψo r ω j j))
  have hex : ∀ j, ∃ I, IsItoC P' ℱ' 𝔚 (ψ' j) I := fun j => exists_isItoC h𝔚 (hψctbl j)
  choose Bj hBj using hex
  have hortho' : ∀ r (ω' : Ω × (ι → WienerSeq)) i j, HasSum (fun a => ψ' i r ω' a * ψ' j r ω' a)
      (if i = j then (1 : ℝ) else 0) := fun r ω' i j => hψo r ω'.1 i j
  have hB : IsCylindricalBrownian P' ℱ' (fun t ω' j => Bj j (t : ℝ) ω') :=
    isCylindricalBrownian_of_itoC h𝔚 hψctbl hBj hortho'
  -- S side
  have hfS : ∀ x, IsCtbl P' ℱ' (fun r ω' (j : ι) => if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) :=
    fun x => pc_isCtbl_comp hπm hπp (pc_ctbl_S hΦ e hSsq hSprog t x (fun r ω x => hψn x r ω))
  have hZ : ∀ x, IsItoC P' ℱ' 𝔚 (fun r ω' => pcXi t Φ x ι r ω'.1)
      (fun τ ω' => inner ℝ (M (min τ t) ω'.1) x) :=
    fun x => pc_Z_isItoC hW hΦ hM ht hπm hπp h𝔚 h𝔚l x
  have hΞ : ∀ x, IsCtbl P' ℱ' (fun r ω' => pcXi t Φ x ι r ω'.1) :=
    fun x => pc_isCtbl_comp hπm hπp (pc_ctbl_pcXi hΦ x t)
  have hsum : ∀ x r (ω' : Ω × (ι → WienerSeq)), Summable fun j : ι =>
      (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) ^ 2 := fun x r ω' => by
    by_cases hr : r ≤ t
    · simpa [hr] using (hψn x r ω'.1).summable
    · simp [hr]
  have hE2 : ∀ x (s : Finset ι) r (ω' : Ω × (ι → WienerSeq)), HasSum
      (fun a => (pcXi t Φ x ι r ω'.1 a - ∑ j ∈ s, (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) *
        ψ' j r ω' a) ^ 2)
      (∑' j, if j ∈ s then 0 else (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) ^ 2) := by
    intro x s r ω'
    by_cases hr : r ≤ t
    · have h := hψt s x r ω'.1
      have e1 : (fun a => (pcXi t Φ x ι r ω'.1 a - ∑ j ∈ s,
          (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) * ψ' j r ω' a) ^ 2) =
          fun a => (Sum.elim (fun k => inner ℝ (Φ r ω'.1 k) x) (fun _ => (0 : ℝ)) a -
            ∑ j ∈ s, inner ℝ (S r ω'.1 (e j)) x * ψ j r ω'.1 a) ^ 2 := by
        funext a; simp [pcXi, hr, hψ']
      rw [e1]
      simpa [hr] using h
    · have e1 : (fun a => (pcXi t Φ x ι r ω'.1 a - ∑ j ∈ s,
          (if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0) * ψ' j r ω' a) ^ 2) = fun _ => 0 := by
        funext a; rcases a with k | l <;> simp [pcXi, hr]
      rw [e1]
      simpa [hr] using hasSum_zero
  have hbridge : ∀ x τ, 0 ≤ τ → Tendsto (fun s : Finset ι => ∫⁻ ω', ‖itoIntegral P' ℱ'
      (fun t ω' (k : s) => (fun t ω' j => Bj j (t : ℝ) ω') t ω' k)
      (fun r ω' (k : s) => (if r ≤ t then inner ℝ (S r ω'.1 (e k)) x else 0)) τ ω' -
        inner ℝ (M (min τ t) ω'.1) x‖ₑ ^ 2 ∂P') atTop (𝓝 0) := fun x τ hτ =>
    pc_bridge h𝔚 hψctbl hBj hB hortho' (hfS x) (hΞ x) (hZ x) (hsum x) (hE2 x) τ hτ
  have hZB : ∀ x, IsItoC P' ℱ' (fun t ω' j => Bj j (t : ℝ) ω')
      (fun r ω' (j : ι) => if r ≤ t then inner ℝ (S r ω'.1 (e j)) x else 0)
      (fun τ ω' => inner ℝ (M (min τ t) ω'.1) x) := fun x =>
    ⟨(hZ x).cont, (hZ x).adapted, (hZ x).zero, fun τ hτ => hbridge x τ hτ⟩
  -- the Gaussian part
  have hBp : ∀ ω' : Ω × (ι → WienerSeq), True := fun _ => trivial
  obtain ⟨G, hGI, hGJ⟩ := pc_exists_G hD (P := P') (ℱ := ℱ') hB
  have hGmeas : Measurable (G t) := (hGI.adapted t).mono (ℱ'.le t) le_rfl
  have hle0 : (𝒢.1.comap (Prod.fst : Ω × (ι → WienerSeq) → Ω)) ≤ ℱ' 0 :=
    (MeasurableSpace.comap_mono (𝒢.2)).trans (le_sup_of_le_left le_sup_left)
  have hGauss := pc_G_gaussian hD hB hGJ ht hGmeas ⟨_, hle0⟩
  refine ⟨Ω × (ι → WienerSeq), inferInstance, P', inferInstance, Prod.fst, hπp, ℱ', ι, hι, e,
    fun t ω' j => Bj j (t : ℝ) ω', S, Sb, G, ?_, hB, ?_, hSsq, ?_, hSb, hGI, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    exact le_sup_of_le_left le_sup_left
  · exact indep_of_indep_of_le_left (indep_zero_cylPath hB) hle0
  · refine ⟨fun ω' => (hM.cont ω'.1).comp (continuous_id.min continuous_const), fun τ => ?_,
      fun τ hτ ω' => ?_, fun τ hτ x => ?_⟩
    · exact ((hM.adapted (min τ t)).mono (ℱ.mono (min_le_left τ t)) le_rfl).comp (hπm τ)
    · simp [hM.zero (min τ t) ((min_le_left τ t).trans hτ) ω'.1]
    · have h1 := hbridge x τ hτ
      refine h1.congr (fun s => ?_)
      have e1 : (fun r (ω' : Ω × (ι → WienerSeq)) (k : s) =>
          if r ≤ t then inner ℝ (S r ω'.1 (e k)) x else 0) =
          fun r ω' (k : s) => inner ℝ (if r ≤ t then S r ω'.1 (e k) else 0) x := by
        funext r ω' k; by_cases hr : r ≤ t <;> simp [hr]
      rw [e1]
  · exact hGmeas.aemeasurable
  · exact hGauss.1
  · exact hGauss.2.1
  · intro x y
    rw [hGauss.2.2 x y]
    exact setIntegral_congr_fun measurableSet_Icc (fun σ hσ => (hSb σ hσ).sq x y)
  · have hMm : Measurable (fun ω' : Ω × (ι → WienerSeq) => M t ω'.1) :=
      ((hM.adapted t).mono (ℱ.le t) le_rfl).comp measurable_fst
    have h1 := pc_L2_bound hD (P := P') (ℱ := ℱ') hB ht (fun r ω' => S r ω'.1)
      (fun x y => isProgressive_comp_π hπm (hSprog x y)) hfS
      (Z := fun x τ ω' => inner ℝ (M (min τ t) ω'.1) x) hZB hGJ hGmeas hMm
      (fun x => Eventually.of_forall fun ω' => by simp)
      (fun r ω' => traceNormForm (hsCovForm (Φ r ω'.1) - sb r)) (fun r hr ω' => by
        have hC := isTraceClassCov_hsCovForm ((hΦ 0).summable r ω'.1)
        have hC' := hsb.traceClass r hr
        obtain ⟨T1, hT1, -⟩ := hC.hasSum_basis e
        obtain ⟨T2, hT2, -⟩ := hC'.hasSum_basis e
        exact powers_stormer e (hSsq r ω'.1) (hSb r hr) hC hC' hT1.summable hT2.summable)
    refine h1.trans (le_of_eq ?_)
    rw [hπp.lintegral_comp (pc_meas_Lr hΦ t sb hsb), pc_lintegral_covDisc hΦ ht sb hsb]

/-- Corollary A.23, display `B:eq:hilbert-martingale-w2` (source lines 10646-10651):
`W₂²(Law M_t, N(0, ∫_0^t Σ̄_r dr)) ≤ E ∫_0^t ‖Σ_r - Σ̄_r‖_{𝔖₁} dr`, for every centered Gaussian
law with that covariance.

PLAN: `hilbert_polar_coupling` gives the coupling `(M_t ∘ π, G_t)` on `Ω'`; `law P' (M_t ∘ π) =
law P (M_t)` by measure preservation and `law P' (G_t) = γ` by uniqueness of the centered Gaussian
law with a given covariance (`HilbertCLTAux.charFun_centered_gaussian` and the characteristic
function determines the law, `Measure.ext_of_charFun`); conclude with `wassersteinE_le_of_coupling`
(`HRS/Prob/Metrics.lean`) and `ENNReal.rpow` bookkeeping (`wassersteinE` is `(∫⁻ ‖x-y‖^2)^{1/2}`). -/
theorem hilbert_martingale_w2 (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    (Φ : ℝ → Ω → κ → H) (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ)
    (M : ℝ → Ω → H) (hM : IsHilbertItoIntegral P ℱ W Φ M)
    (sb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)) (hsb : IsDetCovDensity t sb)
    (γ : Measure H) (hγ : IsGaussianWithIntegratedCov t sb γ) :
    wassersteinE 2 (law P (M t)) γ ^ (2 : ℝ) ≤
      ENNReal.ofReal (covDiscrepancy P t (fun r ω => hsCovForm (Φ r ω)) sb) := by
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', ι, hι, e, B, S, Sb, G, -, -, -, -, -, -, -, hGm, -, hGc,
    hGcov, hbound⟩ := hilbert_polar_coupling P ℱ t ht ⟨⊥, bot_le⟩ W hW Φ hΦ M hM sb hsb
  obtain ⟨hγp, hγc, hγcov⟩ := hγ
  have hMm : AEMeasurable (M t) P := (Measurable.mono (hM.adapted t) (ℱ.le t) le_rfl).aemeasurable
  have hMπ : AEMeasurable (fun ω' => M t (π ω')) P' :=
    hMm.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving
  have := hγp
  have h1 : law P' (fun ω' => M t (π ω')) = law P (M t) := by
    show P'.map (M t ∘ π) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (by rwa [hπ.map_eq]) hπ.aemeasurable, hπ.map_eq]
  have h2 : law P' (G t) = γ := by
    haveI := hGc.1
    refine Measure.ext_of_charFun (funext fun u => ?_)
    rw [HilbertCLTAux.charFun_centered_gaussian hGc, HilbertCLTAux.charFun_centered_gaussian hγc,
      hGcov, hγcov]
  have key := wassersteinE_le_of_coupling P' 2 (by norm_num) (fun ω' => M t (π ω')) (G t) hMπ hGm
  rw [h1, h2] at key
  have key2 := ENNReal.rpow_le_rpow key (show (0:ℝ) ≤ 2 by norm_num)
  refine key2.trans ?_
  rw [← ENNReal.rpow_mul]
  have h3 : ∀ ω' : Ω', ENNReal.ofReal (‖M t (π ω') - G t ω'‖ ^ (2:ℝ)) =
      ‖M t (π ω') - G t ω'‖ₑ ^ 2 := fun ω' => by
    rw [Real.rpow_two, ← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  simp only [h3]
  norm_num
  exact hbound

end Polar

/-! ### Corollary A.24: adding the initial term and the remainder -/

section Assembly

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-! Route for Corollary A.24: `assembly_wp` is the triangle inequality for `W_p` through
`I_emp + M_t` and `I_emp + G_t` (identity coupling with cost `E‖R‖^p`, the given coupling with cost
`E‖M_t - G_t‖^p`, and `wassersteinE_add_indep_le`, the convolution contraction obtained by pushing a
coupling of `(Law I_emp, Law I)` forward under `(a, b, g) ↦ (a + g, b + g)` with `g ∼ Law G_t`
independent of `𝒢`). -/

lemma law_add_indep (𝒢 : SubSigma Ω mΩ) (A G : Ω → H)
    (hA : Measurable[𝒢.1] A) (hG : AEMeasurable G P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap G inferInstance) P) :
    law P (fun ω => A ω + G ω) = ((law P A).prod (law P G)).map (fun z : H × H => z.1 + z.2) := by
  have hAm : Measurable A := hA.mono 𝒢.2 le_rfl
  have hIA : IndepFun A G P := indep_of_indep_of_le_left hind hA.comap_le
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hAm.aemeasurable hG).1 hIA
  have hm : AEMeasurable (fun ω => (A ω, G ω)) P := hAm.aemeasurable.prodMk hG
  rw [← h1, AEMeasurable.map_map_of_aemeasurable (by fun_prop) hm]
  rfl

lemma wassersteinE_add_indep_le (p : ℝ) (hp : 1 ≤ p) (𝒢 : SubSigma Ω mΩ) (A B G : Ω → H)
    (hA : Measurable[𝒢.1] A) (hB : Measurable[𝒢.1] B) (hG : AEMeasurable G P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap G inferInstance) P) :
    wassersteinE p (law P fun ω => A ω + G ω) (law P fun ω => B ω + G ω) ≤
      wassersteinE p (law P A) (law P B) := by
  have hp0 : 0 < p := by linarith
  have hAm : Measurable A := hA.mono 𝒢.2 le_rfl
  have hBm : Measurable B := hB.mono 𝒢.2 le_rfl
  set γ : Measure H := law P G with hγ
  have : IsProbabilityMeasure γ := inferInstance
  have : IsProbabilityMeasure (law P A) := inferInstance
  have : IsProbabilityMeasure (law P B) := inferInstance
  rw [law_add_indep P 𝒢 A G hA hG hind, law_add_indep P 𝒢 B G hB hG hind]
  refine le_iInf fun π => ?_
  obtain ⟨π, hπ⟩ := π
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hkey : ∀ (f : H × H → H), Measurable f → ∀ (ρ : Measure H), π.map f = ρ →
      ((π.prod γ).map (fun w : (H × H) × H => f w.1 + w.2)) =
        (ρ.prod γ).map (fun z : H × H => z.1 + z.2) := by
    intro f hf ρ hρ
    have e1 : (fun w : (H × H) × H => f w.1 + w.2) =
        (fun z : H × H => z.1 + z.2) ∘ (Prod.map f id) := by ext w <;> simp
    rw [e1, ← Measure.map_map (by fun_prop) (by fun_prop), ← hρ]
    congr 1
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
  set T : (H × H) × H → H × H := fun w => (w.1.1 + w.2, w.1.2 + w.2) with hT
  have hTm : Measurable T := by rw [hT]; fun_prop
  have hcoup : IsCoupling ((π.prod γ).map T)
      (((law P A).prod γ).map (fun z : H × H => z.1 + z.2))
      (((law P B).prod γ).map (fun z : H × H => z.1 + z.2)) := by
    constructor
    · rw [Measure.map_map measurable_fst hTm]
      exact hkey Prod.fst measurable_fst _ hπ.1
    · rw [Measure.map_map measurable_snd hTm]
      exact hkey Prod.snd measurable_snd _ hπ.2
  refine (wassersteinE_le_cost hcoup).trans ?_
  refine le_of_eq ?_
  congr 1
  rw [lintegral_map (by fun_prop) hTm]
  have : ∀ w : (H × H) × H, ENNReal.ofReal (‖(T w).1 - (T w).2‖ ^ p) =
      ENNReal.ofReal (‖w.1.1 - w.1.2‖ ^ p) := fun w => by
    simp [hT]
  simp only [this]
  rw [lintegral_prod _ (by fun_prop)]
  simp

lemma assembly_wp (p : ℝ) (hp : 1 ≤ p) (𝒢 : SubSigma Ω mΩ)
    (Iemp I R Mt Gt : Ω → H)
    (hIemp : Measurable[𝒢.1] Iemp) (hI : Measurable[𝒢.1] I)
    (hR : AEMeasurable R P) (hMt : AEMeasurable Mt P) (hGt : AEMeasurable Gt P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap Gt inferInstance) P) :
    wassersteinE p (law P fun ω => Iemp ω + Mt ω + R ω) (law P fun ω => I ω + Gt ω) ≤
      wassersteinE p (law P Iemp) (law P I) +
        (∫⁻ ω, ENNReal.ofReal (‖Mt ω - Gt ω‖ ^ p) ∂P) ^ (1 / p) +
        (∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P) ^ (1 / p) := by
  have hIm : AEMeasurable Iemp P := (hIemp.mono 𝒢.2 le_rfl).aemeasurable
  have hI'm : AEMeasurable I P := (hI.mono 𝒢.2 le_rfl).aemeasurable
  have h1 : AEMeasurable (fun ω => Iemp ω + Mt ω + R ω) P := (hIm.add hMt).add hR
  have h2 : AEMeasurable (fun ω => Iemp ω + Mt ω) P := hIm.add hMt
  have h3 : AEMeasurable (fun ω => Iemp ω + Gt ω) P := hIm.add hGt
  have h4 : AEMeasurable (fun ω => I ω + Gt ω) P := hI'm.add hGt
  have : IsProbabilityMeasure (law P fun ω => Iemp ω + Mt ω + R ω) := inferInstance
  have : IsProbabilityMeasure (law P fun ω => Iemp ω + Mt ω) := inferInstance
  have : IsProbabilityMeasure (law P fun ω => Iemp ω + Gt ω) := inferInstance
  have : IsProbabilityMeasure (law P fun ω => I ω + Gt ω) := inferInstance
  have t1 := wassersteinE_triangle p hp (law P fun ω => Iemp ω + Mt ω + R ω)
    (law P fun ω => Iemp ω + Mt ω) (law P fun ω => I ω + Gt ω)
  have t2 := wassersteinE_triangle p hp (law P fun ω => Iemp ω + Mt ω)
    (law P fun ω => Iemp ω + Gt ω) (law P fun ω => I ω + Gt ω)
  have c1 := wassersteinE_le_of_coupling P p hp _ _ h1 h2
  have c2 := wassersteinE_le_of_coupling P p hp _ _ h2 h3
  have c3 := wassersteinE_add_indep_le P p hp 𝒢 Iemp I Gt hIemp hI hGt hind
  have e1 : ∀ ω, ‖Iemp ω + Mt ω + R ω - (Iemp ω + Mt ω)‖ = ‖R ω‖ := fun ω => by
    rw [add_sub_cancel_left]
  have e2 : ∀ ω, ‖Iemp ω + Mt ω - (Iemp ω + Gt ω)‖ = ‖Mt ω - Gt ω‖ := fun ω => by
    rw [add_sub_add_left_eq_sub]
  simp only [e1, e2] at c1 c2
  calc _ ≤ _ := t1
    _ ≤ (∫⁻ ω, ENNReal.ofReal (‖R ω‖ ^ p) ∂P) ^ (1 / p) +
        ((∫⁻ ω, ENNReal.ofReal (‖Mt ω - Gt ω‖ ^ p) ∂P) ^ (1 / p) +
          wassersteinE p (law P Iemp) (law P I)) := by
      refine add_le_add c1 (t2.trans ?_)
      exact add_le_add c2 c3
    _ = _ := by ring


/-- Corollary A.24 `M:B:cor:hilbert-wasserstein-assembly` (source lines 10672-10692), bound
`B:eq:hilbert-W1-assembly`.  `I_emp, I, R` are `H`-valued random variables with `I_emp`, `I`
measurable with respect to `𝒢 ⊂ ℱ_0`, and `(M_t, G_t)` are coupled as in Corollary A.23: on the
same space, `G_t` centered Gaussian independent of `𝒢` with covariance `∫_0^t Σ̄`, and
`E ‖M_t - G_t‖² ≤ D` (the enlargement of A.23 is the ambient space here).  With
`X := I_emp + M_t + R`, `Y := I + G_t`,
`W₁(Law X, Law Y) ≤ W₁(Law I_emp, Law I) + D^{1/2} + E‖R‖_H`
(in `ℝ≥0∞`; `E‖R‖` is a `lintegral`, so no integrability of `R` is presupposed).

PLAN (lines 10694-10696): triangle inequality `wassersteinE_triangle` for `W₁` through
`I_emp + M_t` and `I_emp + G_t`: the first step is the identity coupling
(`wassersteinE_le_of_coupling` with cost `E‖R‖`), the second the given coupling with cost
`E‖M_t - G_t‖ ≤ (E‖M_t - G_t‖²)^{1/2}` (Jensen, `lintegral_rpow_mono`), the third the
convolution contraction: `Law(I_emp + G_t) = Law(I_emp) * γ`, `Law(I + G_t) = Law(I) * γ` by
independence of `G_t` from `𝒢` (`indepFun_iff_map_prod_eq_prod_map_map`), and
`W₁(ρ₁ * γ, ρ₂ * γ) ≤ W₁(ρ₁, ρ₂)` (push an optimal coupling of `ρ₁, ρ₂` forward by
`(a, b) ↦ (a + g, b + g)` under `π ⊗ γ`). -/
theorem hilbert_wasserstein_assembly_w1 (𝒢 : SubSigma Ω mΩ)
    (Iemp I R Mt Gt : Ω → H)
    (hIemp : Measurable[𝒢.1] Iemp) (hI : Measurable[𝒢.1] I)
    (hR : AEMeasurable R P) (hMt : AEMeasurable Mt P) (hGt : AEMeasurable Gt P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap Gt inferInstance) P)
    (hGauss : IsCenteredGaussian (law P Gt))
    (D : ℝ) (hD : 0 ≤ D) (hcoup : ∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal D) :
    wassersteinE 1 (law P fun ω => Iemp ω + Mt ω + R ω) (law P fun ω => I ω + Gt ω) ≤
      wassersteinE 1 (law P Iemp) (law P I) + ENNReal.ofReal (Real.sqrt D) +
        ∫⁻ ω, ‖R ω‖ₑ ∂P := by
  have h := assembly_wp P 1 le_rfl 𝒢 Iemp I R Mt Gt hIemp hI hR hMt hGt hind
  have e1 : ∀ x : H, ENNReal.ofReal (‖x‖ ^ (1 : ℝ)) = ‖x‖ₑ := fun x => by
    rw [Real.rpow_one, ofReal_norm]
  simp only [e1, div_one, ENNReal.rpow_one] at h
  refine h.trans ?_
  gcongr
  have hm : AEMeasurable (fun ω => ‖Mt ω - Gt ω‖ₑ) P := (hMt.sub hGt).enorm
  have := lintegral_rpow_mono P (fun ω => ‖Mt ω - Gt ω‖ₑ) (p := 1) (q := 2) one_pos one_le_two
  simp only [ENNReal.rpow_one, div_one, ENNReal.rpow_two] at this
  refine this.trans ?_
  have h2 : (∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P) ^ (1 / (2:ℝ)) ≤ (ENNReal.ofReal D) ^ (1 / (2:ℝ)) :=
    ENNReal.rpow_le_rpow hcoup (by norm_num)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hD (by norm_num), Real.sqrt_eq_rpow, one_div]


/-- Corollary A.24, bound `B:eq:hilbert-W2-assembly` (source lines 10685-10690): if all variables
have finite second moments, `W₂(Law X, Law Y) ≤ W₂(Law I_emp, Law I) + D^{1/2} + (E‖R‖²)^{1/2}`.

PLAN: as `hilbert_wasserstein_assembly_w1` with `wassersteinE_triangle` for `p = 2` and
Minkowski's inequality in `L²(Ω;H)` (`eLpNorm_add_le`) for the first two steps; the convolution
contraction for `W₂` is the same push-forward argument. -/
theorem hilbert_wasserstein_assembly_w2 (𝒢 : SubSigma Ω mΩ)
    (Iemp I R Mt Gt : Ω → H)
    (hIemp : Measurable[𝒢.1] Iemp) (hI : Measurable[𝒢.1] I)
    (hIemp2 : MemLp Iemp 2 P) (hI2 : MemLp I 2 P) (hR2 : MemLp R 2 P) (hMt2 : MemLp Mt 2 P)
    (hGt2 : MemLp Gt 2 P)
    (hind : Indep 𝒢.1 (MeasurableSpace.comap Gt inferInstance) P)
    (hGauss : IsCenteredGaussian (law P Gt))
    (D : ℝ) (hD : 0 ≤ D) (hcoup : ∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal D) :
    wassersteinE 2 (law P fun ω => Iemp ω + Mt ω + R ω) (law P fun ω => I ω + Gt ω) ≤
      wassersteinE 2 (law P Iemp) (law P I) + ENNReal.ofReal (Real.sqrt D) +
        (∫⁻ ω, ‖R ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have h := assembly_wp P 2 (by norm_num) 𝒢 Iemp I R Mt Gt hIemp hI hR2.aemeasurable
    hMt2.aemeasurable hGt2.aemeasurable hind
  have e1 : ∀ x : H, ENNReal.ofReal (‖x‖ ^ (2 : ℝ)) = ‖x‖ₑ ^ 2 := fun x => by
    rw [Real.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp only [e1] at h
  refine h.trans ?_
  gcongr
  have h2 : (∫⁻ ω, ‖Mt ω - Gt ω‖ₑ ^ 2 ∂P) ^ (1 / (2:ℝ)) ≤ (ENNReal.ofReal D) ^ (1 / (2:ℝ)) :=
    ENNReal.rpow_le_rpow hcoup (by norm_num)
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg hD (by norm_num), Real.sqrt_eq_rpow, one_div]

end Assembly

/-! ### Remark A.20: the DDS coupling given an initial sigma-field -/

section ConditionalCoupling

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-! ### Route for Remark A.20 (as formalised, on a probability space in `Type`)

The coded path space of `dds_coupling_proof` forgets the original space, so the Brownian motion it
produces cannot be compared with `𝒢`.  Instead the DDS construction is run directly on the product
`Ξ × Wiener` (`Ξ` the original space): the filtration `liftFiltration` contains the pull-back of the
clean (completed) filtration, `liftExtData` verifies the hypotheses of the time change
(`ExtData`), `brownian_core_init` is `ExtData.brownian_core` together with the fact that the
time-changed filtration contains the time-`0` σ-field of the original filtration, and the Brownian
motion `β` is independent of that σ-field. -/

section DDSLift

/-- `exists_enlargement_indep` (`HRS/Stochastic/DDSCore.lean`) for a space `E` in an arbitrary
universe (the proof there does not use `E : Type`). -/
theorem exists_enlargement_indep_univ (ι : Type) [Fintype ι] (E : Type*) [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] :
    ∃ (W : ℝ≥0 → E × (ι → WienerSeq) → ι → ℝ) (hW : ∀ t, Measurable (W t)),
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
      IndepFun Prod.fst (fun p t => W t p) (μ.prod (Measure.pi fun _ : ι => wienerMeasure)) ∧
      IsBrownianFiltration (μ.prod (Measure.pi fun _ : ι => wienerMeasure))
        (generatedFiltration (μ.prod (Measure.pi fun _ : ι => wienerMeasure))
          Prod.fst measurable_fst W hW) W := by
  set ν : Measure (ι → WienerSeq) := Measure.pi fun _ : ι => wienerMeasure with hν
  set W : ℝ≥0 → E × (ι → WienerSeq) → ι → ℝ := fun t p k => wienerPath t (p.2 k) with hWdef
  have hW : ∀ t, Measurable (W t) := fun t =>
    Measurable.of_eval fun k => (measurable_wienerPath t).comp
      ((measurable_pi_apply k).comp measurable_snd)
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => funext fun k => wienerPath_zero _
  have hWc : ∀ ω, Continuous fun t => W t ω := fun ω =>
    continuous_pi fun k => continuous_wienerPath _
  have hX₀W : IndepFun Prod.fst (fun p : E × (ι → WienerSeq) => fun t => W t p) (μ.prod ν) :=
    indepFun_prod (μ := μ) (ν := ν) (X := id)
      (Y := fun (ω : ι → WienerSeq) (t : ℝ≥0) (k : ι) => wienerPath t (ω k)) measurable_id
      (Measurable.of_eval fun t => Measurable.of_eval fun k =>
        (measurable_wienerPath t).comp (measurable_pi_apply k))
  refine ⟨W, hW, hW0, hWc, hX₀W, ?_⟩
  have hsnd : MeasurePreserving (fun p : E × (ι → WienerSeq) => p.2) (μ.prod ν) ν :=
    measurePreserving_snd
  have hev : ∀ k : ι, MeasurePreserving (fun p : E × (ι → WienerSeq) => p.2 k) (μ.prod ν)
      wienerMeasure := fun k =>
    (measurePreserving_eval (fun _ : ι => wienerMeasure) k).comp hsnd
  have hB : ∀ k, IsBrownianReal (fun t p => W t p k) (μ.prod ν) := fun k =>
    IsBrownianReal.comp_measurePreserving (hev k) isPreBrownianReal_wienerPath
      continuous_wienerPath
  have hpath : Measurable fun (ω : WienerSeq) (t : ℝ≥0) => wienerPath t ω :=
    Measurable.of_eval measurable_wienerPath
  have hind0 : iIndepFun (fun (k : ι) (ω : ι → WienerSeq) => fun t : ℝ≥0 => wienerPath t (ω k)) ν :=
    iIndepFun_pi (μ := fun _ : ι => wienerMeasure) (X := fun _ => fun ω t => wienerPath t ω)
      (fun _ => hpath.aemeasurable)
  have hind : iIndepFun (fun (k : ι) (p : E × (ι → WienerSeq)) => fun t : ℝ≥0 => W t p k)
      (μ.prod ν) :=
    iIndepFun_comp_measurePreserving hsnd (X := fun (k : ι) (ω : ι → WienerSeq) =>
      fun t : ℝ≥0 => wienerPath t (ω k))
      (fun k => Measurable.of_eval fun t => (measurable_wienerPath t).comp (measurable_pi_apply k))
      hind0
  exact isBrownianFiltration_generated (μ.prod ν) W hW hB hind hW0 hWc Prod.fst measurable_fst
    hX₀W


variable {Ξ : Type*} {mΞ : MeasurableSpace Ξ}

set_option warn.classDefReducibility false in
/-- The Brownian part of the lifted filtration. -/
def liftWPart (W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ) (u : ℝ) :
    MeasurableSpace (Ξ × (Fin 1 → WienerSeq)) :=
  ⨆ (r : ℝ≥0) (_ : (r : ℝ) ≤ u), MeasurableSpace.comap (W r) inferInstance

/-- `ℱ u = (comap fst (ℱ₁ u) ⊔ σ(W_r, r ≤ u)) ⊔ nullSets`. -/
def liftFiltration (Q' : Measure (Ξ × (Fin 1 → WienerSeq))) (ℱ₁ : Filtration ℝ mΞ)
    (W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ) (hW : ∀ r, Measurable (W r)) :
    Filtration ℝ (inferInstance : MeasurableSpace (Ξ × (Fin 1 → WienerSeq))) where
  seq u := (MeasurableSpace.comap Prod.fst (ℱ₁ u) ⊔ liftWPart W u) ⊔ nullSets Q'
  mono' := by
    intro u u' h
    refine sup_le_sup_right (sup_le_sup ?_ ?_) _
    · exact MeasurableSpace.comap_mono (ℱ₁.mono h)
    · exact iSup₂_mono' fun r hr => ⟨r, hr.trans h, le_rfl⟩
  le' u := sup_le (sup_le ((MeasurableSpace.comap_mono (ℱ₁.le u)).trans measurable_fst.comap_le)
    (iSup₂_le fun r _ => (hW r).comap_le)) (nullSets_le Q')

theorem comap_le_liftFiltration {Q' : Measure (Ξ × (Fin 1 → WienerSeq))} {ℱ₁ : Filtration ℝ mΞ}
    {W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ} {hW : ∀ r, Measurable (W r)} (u : ℝ) :
    MeasurableSpace.comap Prod.fst (ℱ₁ u) ≤ liftFiltration Q' ℱ₁ W hW u :=
  (le_sup_left : MeasurableSpace.comap Prod.fst (ℱ₁ u) ≤ _ ⊔ liftWPart W u).trans le_sup_left

theorem liftWPart_le_liftFiltration {Q' : Measure (Ξ × (Fin 1 → WienerSeq))}
    {ℱ₁ : Filtration ℝ mΞ} {W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ}
    {hW : ∀ r, Measurable (W r)} (u : ℝ) : liftWPart W u ≤ liftFiltration Q' ℱ₁ W hW u :=
  (le_sup_right : liftWPart W u ≤ MeasurableSpace.comap Prod.fst (ℱ₁ u) ⊔ _).trans le_sup_left

theorem liftFiltration_le_generated {Q' : Measure (Ξ × (Fin 1 → WienerSeq))}
    {ℱ₁ : Filtration ℝ mΞ} {W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ}
    {hW : ∀ r, Measurable (W r)} (u : ℝ) :
    liftFiltration Q' ℱ₁ W hW u ≤ generatedFiltration Q' Prod.fst measurable_fst W hW u := by
  refine sup_le_sup_right (sup_le ?_ ?_) _
  · exact (MeasurableSpace.comap_mono (ℱ₁.le u)).trans le_sup_left
  · exact le_sup_right

theorem liftWPart_le_comap_path (W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ) (u : ℝ) :
    liftWPart W u ≤ MeasurableSpace.comap (fun p τ => W τ p) inferInstance := by
  refine iSup₂_le fun r _ => ?_
  have : (W r) = (fun f : ℝ≥0 → Fin 1 → ℝ => f r) ∘ (fun p τ => W τ p) := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply r).comap_le

theorem martingale_lift (Q : Measure Ξ) [IsProbabilityMeasure Q] {ℱ₁ : Filtration ℝ mΞ}
    {Y : ℝ → Ξ → ℝ} (hY : Martingale Y ℱ₁ Q)
    {W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ} (hW : ∀ r, Measurable (W r))
    (hind : IndepFun Prod.fst (fun p τ => W τ p)
      (Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure))) :
    Martingale (fun τ (p : Ξ × (Fin 1 → WienerSeq)) => Y τ p.1)
      (liftFiltration (Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure)) ℱ₁ W hW)
      (Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure)) := by
  set ν : Measure (Fin 1 → WienerSeq) := Measure.pi fun _ : Fin 1 => wienerMeasure with hν
  set Q' := Q.prod ν with hQ'
  have hfst : MeasurePreserving (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ) Q' Q :=
    measurePreserving_fst
  have hint : ∀ τ, Integrable (fun p : Ξ × (Fin 1 → WienerSeq) => Y τ p.1) Q' := fun τ =>
    hfst.integrable_comp_of_integrable (hY.integrable τ)
  have hfm : ∀ τ, StronglyMeasurable[MeasurableSpace.comap Prod.fst inferInstance]
      (fun p : Ξ × (Fin 1 → WienerSeq) => Y τ p.1) := fun τ =>
    (((hY.1 τ).measurable.mono (ℱ₁.le τ) le_rfl).comp
      (comap_measurable (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ))).stronglyMeasurable
  have hgm : ∀ τ, StronglyMeasurable[MeasurableSpace.comap Prod.fst (ℱ₁ τ)]
      (fun p : Ξ × (Fin 1 → WienerSeq) => Y τ p.1) := fun τ =>
    ((hY.1 τ).measurable.comp
      (comap_measurable (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ))).stronglyMeasurable
  refine ⟨fun τ => (hgm τ).mono (comap_le_liftFiltration τ), fun s r hsr => ?_⟩
  have hind' : Indep (MeasurableSpace.comap Prod.fst inferInstance :
      MeasurableSpace (Ξ × (Fin 1 → WienerSeq))) (liftWPart W s) Q' :=
    indep_of_indep_of_le_right ((IndepFun_iff_Indep _ _ _).1 hind) (liftWPart_le_comap_path W s)
  have hle1 : MeasurableSpace.comap Prod.fst (ℱ₁ s) ≤ (MeasurableSpace.comap Prod.fst inferInstance :
      MeasurableSpace (Ξ × (Fin 1 → WienerSeq))) := MeasurableSpace.comap_mono (ℱ₁.le s)
  have hle2 : (MeasurableSpace.comap Prod.fst inferInstance :
      MeasurableSpace (Ξ × (Fin 1 → WienerSeq))) ≤
      (inferInstance : MeasurableSpace (Ξ × (Fin 1 → WienerSeq))) := measurable_fst.comap_le
  have hle3 : liftWPart W s ≤ (inferInstance : MeasurableSpace (Ξ × (Fin 1 → WienerSeq))) :=
    (liftWPart_le_liftFiltration (Q' := Q') (ℱ₁ := ℱ₁) (hW := hW) s).trans
      ((liftFiltration Q' ℱ₁ W hW).le s)
  have e1 : Q'[fun p : Ξ × (Fin 1 → WienerSeq) => Y r p.1 | liftFiltration Q' ℱ₁ W hW s] =ᵐ[Q']
      Q'[fun p : Ξ × (Fin 1 → WienerSeq) => Y r p.1 |
        MeasurableSpace.comap Prod.fst (ℱ₁ s) ⊔ liftWPart W s] :=
    condExp_sup_nullSets (sup_le (hle1.trans hle2) hle3) _
  have e2 := condExp_sup_of_indep (P := Q') (𝒜 := MeasurableSpace.comap Prod.fst (ℱ₁ s)) hle2 hle3
    hle1 hind' (hint r) (hfm r)
  have e3 : (fun p : Ξ × (Fin 1 → WienerSeq) => Y s p.1) =ᵐ[Q']
      Q'[fun p : Ξ × (Fin 1 → WienerSeq) => Y r p.1 | MeasurableSpace.comap Prod.fst (ℱ₁ s)] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (hle1.trans hle2) (hint r)
      (fun S _ _ => (hint s).integrableOn) (fun S hS _ => ?_) (hgm s).aestronglyMeasurable
    obtain ⟨H, hH, rfl⟩ := hS
    have hHfull : MeasurableSet H := ℱ₁.le s _ hH
    have key : ∀ τ, ∫ p in (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ) ⁻¹' H, Y τ p.1 ∂Q' =
        ∫ ω in H, Y τ ω ∂Q := by
      intro τ
      have h1 := setIntegral_map (μ := Q') (g := (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ))
        (f := Y τ) hHfull
        (by rw [hfst.map_eq]; exact ((hY.1 τ).measurable.mono (ℱ₁.le τ) le_rfl).aestronglyMeasurable)
        measurable_fst.aemeasurable
      rw [hfst.map_eq] at h1
      exact h1.symm
    rw [key s, key r]
    exact hY.setIntegral_eq hsr hH
  exact e1.trans (e2.trans e3.symm)

theorem liftExtData {Q : Measure Ξ} [IsProbabilityMeasure Q] {ℱ₁ : Filtration ℝ mΞ} {t : ℝ}
    {M A : ℝ → Ξ → ℝ} (hc : CleanData Q ℱ₁ t M A) (ht : 0 ≤ t) :
    ∃ (W : ℝ≥0 → Ξ × (Fin 1 → WienerSeq) → Fin 1 → ℝ) (hW : ∀ r, Measurable (W r)),
      ExtData (Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure))
        (liftFiltration (Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure)) ℱ₁ W hW) W t
        (fun τ p => M τ p.1) (fun τ p => A τ p.1) := by
  obtain ⟨W, hW, hW0, hWc, hind, hBF⟩ := exists_enlargement_indep_univ (Fin 1) Ξ Q
  refine ⟨W, hW, ?_⟩
  set P' := Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure) with hP'
  have hfst : MeasurePreserving (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ) P' Q :=
    measurePreserving_fst
  have hcomplete : IsCompleteFiltration P' (liftFiltration P' ℱ₁ W hW) := by
    intro u S hS hP
    have h1 : MeasurableSet[nullSets P'] S := MeasurableSpace.measurableSet_generateFrom ⟨hS, hP⟩
    exact (le_sup_right : nullSets P' ≤ _) S h1
  refine
    { bf := IsBrownianFiltration.of_le_of_adapted hBF (fun u => liftFiltration_le_generated u)
        hcomplete (fun u => ?_)
      ht := ht
      mart := martingale_lift Q hc.mart hW hind
      qmart := martingale_lift Q hc.qmart hW hind
      memLp := fun τ hτ => (hc.memLp τ hτ).comp_measurePreserving hfst
      adaptedA := fun τ => ((hc.adaptedA τ).comp
        (comap_measurable (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ))).mono
          (comap_le_liftFiltration τ) le_rfl
      zeroM := fun p => hc.zeroM p.1
      zeroA := fun p => hc.zeroA p.1
      contM := fun p => (hc.contM p.1)
      contA := fun p => (hc.contA p.1)
      monoA := fun p => (hc.monoA p.1) }
  exact Measurable.of_comap_le ((le_iSup₂_of_le u le_rfl le_rfl :
      MeasurableSpace.comap (W u) inferInstance ≤ liftWPart W (u : ℝ)).trans
        (liftWPart_le_liftFiltration (Q' := P') (ℱ₁ := ℱ₁) (hW := hW) (u : ℝ)))

end DDSLift

section DDSCoreInit

variable {Ω₂ : Type*} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝒢 : Filtration ℝ m₂} {W : ℝ≥0 → Ω₂ → Fin 1 → ℝ} {t : ℝ} {M' A' : ℝ → Ω₂ → ℝ}

/-- `ExtData.brownian_core` (`HRS/Stochastic/DDSCore.lean`) together with the fact that the
time-changed filtration contains the time-`0` σ-field of the original one (`𝒢_0 ≤ 𝒢_{S_v}` since
`S_v ≥ 0`). -/
theorem ExtData.brownian_core_init (h : ExtData P₂ 𝒢 W t M' A') :
    ∃ (ℱ' : Filtration ℝ m₂) (β : ℝ≥0 → Ω₂ → Fin 1 → ℝ), IsBrownianFiltration P₂ ℱ' β ∧ (∀ u, 𝒢 0 ≤ ℱ' u) ∧
      (∀ τ ∈ Set.Icc 0 t, IsStoppingTime ℱ' fun ω => ((max (A' τ ω) 0 : ℝ) : WithTop ℝ)) ∧
      (∀ᵐ ω ∂P₂, ∀ τ ∈ Set.Icc 0 t, M' τ ω = β (Real.toNNReal (A' τ ω)) ω 0) := by
  classical
  have hT := h.tcData
  obtain ⟨hcomp, hadapt, hzero, hcont, hmart, hqv⟩ := timeChange_levy_hypotheses hT
  set ℱ' := timeChangedFiltration P₂ 𝒢 (Aext A' t) hT.adapted hT.contA with hℱ'
  set β0 : ℝ → Ω₂ → ℝ := tcProcess (Mext W M' t) (Aext A' t) with hβ0
  have hβ0max : ∀ u ω, β0 (max u 0) ω = β0 u ω := fun u ω => by
    simp only [hβ0, tcProcess, levelTimeR_max_zero (hT.zeroA ω)]
  have hmeas : ∀ u : ℝ≥0, Measurable (fun ω => β0 u ω) := fun u => hT.measurable_tcProcess (u : ℝ)
  have hcont' : ∀ᵐ ω ∂P₂, Continuous fun u : ℝ≥0 => β0 u ω :=
    hcont.mono fun ω hω => hω.comp NNReal.continuous_coe
  obtain ⟨Y, hYm, hYc, hYae⟩ := exists_continuous_modification P₂ (fun (u : ℝ≥0) ω => β0 u ω) hmeas hcont'
  set βs : ℝ≥0 → Ω₂ → ℝ := fun u ω => Y u ω - Y 0 ω with hβs
  have hY0 : ∀ᵐ ω ∂P₂, Y 0 ω = 0 := by
    filter_upwards [hYae] with ω hω
    rw [hω 0]; exact hzero ω
  have hβsae : ∀ᵐ ω ∂P₂, ∀ u : ℝ≥0, βs u ω = β0 u ω := by
    filter_upwards [hYae, hY0] with ω h1 h2 u
    simp only [hβs, h1 u, h2, sub_zero]
  have hβsm : ∀ u, Measurable (βs u) := fun u => (hYm u).sub (hYm 0)
  -- real-time version
  have hβsR : ∀ u : ℝ, (fun ω => ofNNRealTime βs u ω) =ᵐ[P₂] β0 u := by
    intro u
    filter_upwards [hβsae] with ω hω
    simp only [ofNNRealTime_apply]
    rw [hω, ← hβ0max u ω]
    congr 1
  have hβsad : ∀ u : ℝ, Measurable[ℱ' u] (fun ω => ofNNRealTime βs u ω) := fun u =>
    hcomp.measurable_of_ae_eq u (hadapt u)
      ((hβsm _)) (hβsR u).symm
  refine ⟨ℱ', fun u ω _ => βs u ω, ?_, ?_, ?_, ?_⟩
  · refine levy_characterization P₂ ℱ' hcomp (fun u ω _ => βs u ω) ?_ ?_ ?_ ?_ ?_
    · intro u
      have hb := hβsad (u : ℝ)
      letI : MeasurableSpace Ω₂ := ℱ' u
      exact measurable_pi_iff.2 fun _ => by simpa using hb
    · intro ω; funext k; simp [hβs]
    · intro ω; exact continuous_pi fun _ => (hYc ω).sub continuous_const
    · intro k
      refine martingale_congr_ae hmart (fun u => (hβsad u).stronglyMeasurable) hβsR
    · intro k l
      have hkl : k = l := Subsingleton.elim k l
      subst hkl
      refine martingale_congr_ae hqv (fun u => ?_) (fun u => ?_)
      · simp only [ite_true]
        exact (((hβsad u).mul (hβsad u)).sub measurable_const).stronglyMeasurable
      · simp only [ite_true]
        filter_upwards [hβsR u] with ω hω
        simp only [ofNNRealTime_apply] at hω ⊢
        rw [hω]
  · intro u
    show 𝒢 0 ≤ (⨅ (v : ℝ) (_ : u < v),
      (isStoppingTime_levelTime 𝒢 (Aext A' t) hT.adapted hT.contA v).measurableSpace) ⊔
        nullSets P₂
    refine le_trans ?_ (le_sup_left : _ ≤ _ ⊔ nullSets P₂)
    refine le_iInf₂ fun v hv => ?_
    have := (isStoppingTime_const 𝒢 (0 : ℝ)).measurableSpace_mono
      (isStoppingTime_levelTime 𝒢 (Aext A' t) hT.adapted hT.contA v)
      (fun ω => levelTime_nonneg (A := Aext A' t) (ω := ω) v)
    rwa [IsStoppingTime.measurableSpace_const] at this
  · intro τ hτ
    have e := h.Aext_of_mem hτ
    have := isStoppingTime_max_level (P := P₂) (𝒢 := 𝒢) (A := Aext A' t) (hA := hT.adapted)
      (hc := hT.contA) hT.monoA hT.zeroA τ hτ.1
    rw [e] at this
    exact this
  · filter_upwards [hT.ae_const_on_const_of_qv_real, hβsae] with ω hconst hβω τ hτ
    have hAτ : Aext A' t τ ω = A' τ ω := by rw [h.Aext_of_mem hτ]
    have hu0 : 0 ≤ A' τ ω := by
      have h3 : A' 0 ω ≤ A' τ ω := h.monoA ω ⟨le_rfl, h.ht⟩ hτ hτ.1
      rwa [h.zeroA ω] at h3
    set S := levelTimeR (Aext A' t) (A' τ ω) ω with hS
    have hS0 : 0 ≤ S := levelTimeR_nonneg (hT.topA ω) _
    have hSτ : S ≤ τ := levelTimeR_le_of_le (hT.topA ω) (hT.contA ω) (hT.monoA ω) hτ.1
      (le_of_eq (by rw [hAτ]))
    have hAS : Aext A' t S ω = A' τ ω := by
      rw [hS, hT.A_levelTimeR_max' ω, max_eq_left hu0]
    have hc := hconst S τ hS0 hSτ (by rw [hAS, hAτ]) τ ⟨hSτ, le_rfl⟩
    have h1 : β0 (A' τ ω) ω = Mext W M' t S ω := rfl
    have h2 : M' τ ω = Mext W M' t τ ω := by rw [h.Mext_of_mem hτ]
    have h3 : βs (Real.toNNReal (A' τ ω)) ω = β0 (A' τ ω) ω := by
      rw [hβω, hβ0, show ((Real.toNNReal (A' τ ω) : ℝ≥0) : ℝ) = A' τ ω from
        Real.coe_toNNReal _ hu0]
    show M' τ ω = βs (Real.toNNReal (A' τ ω)) ω
    rw [h3, h1, h2, hc]


end DDSCoreInit

section DDSAssembly

universe uΞ

/-- Remark A.20 for a probability space `Ξ : Type uΞ`, with the enlargement `Ξ × Wiener` in the same
universe (the original specification put the enlargement in `Type`, which is false for `Ξ` in a higher universe: an
enlargement in `Type` cannot exist in general, since a measure-preserving `π : Ω' → Ξ` forces
`P` to have a Type-small support): the coupling `G = β_v` with `β` the Dambis–Dubins–Schwarz
Brownian motion of the time-changed filtration, which contains `ℱ_0 ⊇ 𝒢` at time `0`. -/
theorem dds_coupling_conditional {Ξ : Type uΞ} {mΞ : MeasurableSpace Ξ} (Q : Measure Ξ)
    [IsProbabilityMeasure Q] (ℱ : Filtration ℝ mΞ) (t : ℝ) (ht : 0 ≤ t) (𝒢 : InitialSigma ℱ)
    (M A : ℝ → Ξ → ℝ) (hM : IsContSqMartingale Q ℱ t M) (hA : IsQuadraticVariation Q ℱ t M A)
    (hint : Integrable (A t) Q) (v : ℝ) (hv : 0 ≤ v) :
    ∃ (Ω' : Type uΞ) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ξ) (_ : MeasurePreserving π P' Q) (G : Ω' → ℝ),
      Measurable G ∧
      law P' G = gaussianLaw v ∧
      Indep (𝒢.1.comap π) (MeasurableSpace.comap G inferInstance) P' ∧
      ∫⁻ ω', ‖M t (π ω') - G ω'‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal (∫ ω, |A t ω - v| ∂Q) := by
  classical
  obtain ⟨M₁, A₁, hc, hMae, hAae⟩ := exists_clean hM hA hint
  obtain ⟨W, hW, hext⟩ := liftExtData hc ht
  set P' := Q.prod (Measure.pi fun _ : Fin 1 => wienerMeasure) with hP'
  obtain ⟨ℱ', β, hβ, hinit, hstop, hid⟩ := hext.brownian_core_init
  have hfst : MeasurePreserving (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ) P' Q :=
    measurePreserving_fst
  refine ⟨Ξ × (Fin 1 → WienerSeq), inferInstance, P', inferInstance, Prod.fst, hfst,
    fun p => β (Real.toNNReal v) p 0, ?_, ?_, ?_, ?_⟩
  · exact (measurable_pi_apply 0).comp ((hβ.adapted _).mono (ℱ'.le _) le_rfl)
  · exact (hβ.hasLaw_coord (Real.toNNReal v) 0).map_eq
  · -- independence of `𝒢` and `β_v`
    have h1 : (𝒢.1.comap (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ)) ≤ ℱ' 0 := by
      refine (MeasurableSpace.comap_mono (𝒢.2.trans ?_)).trans
        ((comap_le_liftFiltration (Q' := P') (ℱ₁ := augFiltration Q ℱ) (hW := hW) 0).trans
          (hinit 0))
      exact le_sup_left
    have h2 : MeasurableSpace.comap (fun p : Ξ × (Fin 1 → WienerSeq) => β (Real.toNNReal v) p 0)
        inferInstance ≤ MeasurableSpace.comap
          (fun p => β (Real.toNNReal v) p - β 0 p) inferInstance := by
      have : (fun p : Ξ × (Fin 1 → WienerSeq) => β (Real.toNNReal v) p 0) =
          (fun y : Fin 1 → ℝ => y 0) ∘ (fun p => β (Real.toNNReal v) p - β 0 p) := by
        funext p; simp [hβ.zero p]
      rw [this, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_pi_apply 0).comap_le
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right
      (hβ.indep_incr 0 (Real.toNNReal v) zero_le).symm h2) h1
  · have hAm : Measurable (A₁ t) := (hc.adaptedA t).mono ((augFiltration Q ℱ).le t) le_rfl
    have hS0 : ∀ p : Ξ × (Fin 1 → WienerSeq), 0 ≤ max (A₁ t p.1) 0 := fun p => le_max_right _ _
    have hSint : Integrable (fun p : Ξ × (Fin 1 → WienerSeq) => max (A₁ t p.1) 0) P' :=
      hfst.integrable_comp_of_integrable (g := fun ω => max (A₁ t ω) 0) hc.intA.pos_part
    have hbound := brownian_stopped_L2_bound hβ 0 (fun p => max (A₁ t p.1) 0) hS0
      (hstop t ⟨ht, le_rfl⟩) hSint v hv
    simp_rw [toNNReal_max_zero] at hbound
    have hAnn : ∀ ω, 0 ≤ A₁ t ω := fun ω => by
      have h3 : A₁ 0 ω ≤ A₁ t ω := hc.monoA ω ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
      rwa [hc.zeroA ω] at h3
    have hint_eq : ∫ p, |max (A₁ t p.1) 0 - v| ∂P' = ∫ ω, |A t ω - v| ∂Q := by
      have hg : Measurable fun ω => |max (A₁ t ω) 0 - v| := ((hAm.max measurable_const).sub_const v).abs
      have h1 := integral_map (μ := P') (φ := (Prod.fst : Ξ × (Fin 1 → WienerSeq) → Ξ))
        hfst.measurable.aemeasurable (f := fun ω => |max (A₁ t ω) 0 - v|) hg.aestronglyMeasurable
      rw [hfst.map_eq] at h1
      rw [← h1]
      refine integral_congr_ae ?_
      filter_upwards [hAae t] with ω hω
      rw [max_eq_left (hAnn ω), hω]
    have e1 : ∀ᵐ p ∂P', M t p.1 = β (Real.toNNReal (A₁ t p.1)) p 0 := by
      have h0 := hfst.quasiMeasurePreserving.ae_eq_comp (hMae t)
      filter_upwards [h0, hid] with p h1 h2
      exact h1.symm.trans (h2 t ⟨ht, le_rfl⟩)
    calc ∫⁻ p, ‖M t p.1 - β (Real.toNNReal v) p 0‖ₑ ^ 2 ∂P'
        = ∫⁻ p, ‖β (Real.toNNReal (A₁ t p.1)) p 0 - β (Real.toNNReal v) p 0‖ₑ ^ 2 ∂P' :=
          lintegral_congr_ae (by filter_upwards [e1] with p hp; rw [hp])
      _ ≤ ENNReal.ofReal (∫ p, |max (A₁ t p.1) 0 - v| ∂P') := hbound
      _ = _ := by rw [hint_eq]

end DDSAssembly


end ConditionalCoupling

/-! ### Remarks 3.8, A.25 and A.32: several observation times through one vector martingale -/

section MultiTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
variable (P : Measure Ω) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

/-- The integrand "killed after `t_a`": `1_{r < t_a} Φ_r` (Remark A.32's display
`B:newprob:stopped-integrands`, line 11043; Remark 3.8 says "extend the integrand by zero on
`(t_a, t_q]`", which differs only at the single time `r = t_a`). -/
def killAfter (Φ : ℝ → Ω → ι → ℝ) (ta : ℝ) : ℝ → Ω → ι → ℝ :=
  fun r ω => Set.indicator (Set.Iio ta) (fun _ => Φ r ω) r

/-- The covariation density of the killed vector: `Σ^{ab}_r = 1_{r < min(t_a,t_b)} ∑_k Φ^{a,k}_r Φ^{b,k}_r`
(`B:newprob:stopped-integrands`, line 11044; `B:eq:qv-cross` with the extended integrands). -/
def killedCovMatrix {p : ℕ} (Φ : Fin p → ℝ → Ω → ι → ℝ) (ts : Fin p → ℝ) :
    ℝ → Ω → Matrix (Fin p) (Fin p) ℝ :=
  fun r ω => Matrix.of fun a b => if r < min (ts a) (ts b) then ∑ k, Φ a r ω k * Φ b r ω k else 0

omit [IsProbabilityMeasure P] in
/-- Indicator of a measurable time set `S` applied to a progressive `L²` integrand is progressive
and `L²` (`1_S(r) Φ_r`). -/
theorem isProgressiveL2_indicator_set {Φ : ℝ → Ω → ι → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hΦ : IsProgressiveL2 P ℱ Φ) :
    IsProgressiveL2 P ℱ (fun r ω => Set.indicator S (fun _ => Φ r ω) r) := by
  refine ⟨?_, fun T => ?_⟩
  · intro i
    have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
        {p : Set.Iic i × Ω | (p.1 : ℝ) ∈ S} :=
      hS.preimage (measurable_subtype_coe.comp
        (@measurable_fst (Set.Iic i) Ω Subtype.instMeasurableSpace (ℱ i)))
    have := (hΦ.prog i).indicator hset
    convert this using 1
    funext p
    beta_reduce
    by_cases hp : (p.1 : ℝ) ∈ S
    · have hp' : p ∈ {p : Set.Iic i × Ω | (p.1 : ℝ) ∈ S} := hp
      rw [Set.indicator_of_mem hp (f := fun _ => Φ p.1 p.2), Set.indicator_of_mem hp']
    · have hp' : p ∉ {p : Set.Iic i × Ω | (p.1 : ℝ) ∈ S} := hp
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  · refine lt_of_le_of_lt (sqIntegralOn_mono_of_enorm_le (fun s ω k => ?_) T) (hΦ.sq T)
    by_cases hr : s ∈ S <;> simp [Set.indicator, hr]

/-- For `t_a ≥ 0` the killed integrand `1_{r < t_a} Φ_r` and `1_{0 < r ≤ t_a} Φ_r` have the same
`L²` difference on every `[0, T]`: they differ only at `r ∈ {0, t_a}` and for `r < 0`, which are
`dr`-null on `[0, T]` (for `r < 0` they are not in `[0,T]`). -/
theorem sqIntegralOn_killAfter_sub_Ioc (Φ : ℝ → Ω → ι → ℝ) (ta : ℝ) (T : ℝ) :
    sqIntegralOn P (fun s ω => killAfter Φ ta s ω -
      Set.indicator (Set.Ioc 0 ta) (fun _ => Φ s ω) s) T = 0 := by
  have hnull : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0, ta} : Set ℝ) :=
    ((Set.countable_singleton ta).insert 0).ae_notMem volume
  have hinner : ∀ ω, ∫⁻ s in Set.Icc 0 T, ∑ k, ‖(killAfter Φ ta s ω -
      Set.indicator (Set.Ioc 0 ta) (fun _ => Φ s ω) s) k‖ₑ ^ 2 = 0 := by
    intro ω
    have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
        ∑ k, ‖(killAfter Φ ta s ω - Set.indicator (Set.Ioc 0 ta) (fun _ => Φ s ω) s) k‖ₑ ^ 2 = 0 := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (hnull.mono fun s hs hI => ?_)
      have hs0 : s ≠ 0 := fun h => hs (Or.inl h)
      have hsa : s ≠ ta := fun h => hs (Or.inr h)
      have hz : ∀ k, (killAfter Φ ta s ω - Set.indicator (Set.Ioc 0 ta) (fun _ => Φ s ω) s) k = 0 := by
        intro k
        rcases lt_or_gt_of_ne hsa with h | h
        · have hmem : s ∈ Set.Ioc 0 ta := ⟨lt_of_le_of_ne hI.1 (Ne.symm hs0), h.le⟩
          simp [killAfter, Set.indicator_of_mem hmem, h]
        · have hnmem : s ∉ Set.Ioc 0 ta := fun hm => absurd hm.2 (not_le.2 h)
          simp [killAfter, Set.indicator_of_notMem hnmem, not_lt.2 h.le]
      exact Finset.sum_eq_zero fun k _ => by rw [hz k]; simp
    rw [lintegral_congr_ae hae]
    simp
  simp only [sqIntegralOn, hinner]
  simp

/-- Remark 3.8 `M:B:rem:multitime` (source lines 1705-1707), the statable content: for terminal
pairs `(Φ_a, t_a)` with `0 ≤ t_a ≤ t_q` and progressive `L²` integrands `Φ_a`, the martingales
`M[Φ_a]` stopped at their terminal times form a single `ℝ^p`-valued continuous martingale over
`[0, t_q]` with respect to the common filtration (the vector Itô integral of the integrands
extended by zero after `t_a`); its value at `t_q` is the vector `(M^a_{t_a})_a` of the single-time
statistics, and `B:eq:qv-cross` holds with the extended integrands, i.e. its covariation density is
`killedCovMatrix`.  This is also the identification `(M^a_{t_a})_a = M̃_{t_q}` of Remark A.25
(lines 10698-10700) and the first assertion of Remark A.32.

PLAN: `killAfter Φ_a t_a` is `IsProgressiveL2` (indicator of a measurable time set times a
progressive integrand; `sqIntegralOn_mono_of_enorm_le`); `itoIntegral_indicator_Ioc` with
`a = 0, b = t_a` (the integrands `1_{(0,t_a]}Φ` and `1_{[0,t_a)}Φ` differ on a Lebesgue-null set
of times, `itoIntegral_congr`) gives `∫ killAfter Φ_a t_a dW (τ) = M^a_{min τ t_a}` for all `τ`
a.s.; the covariation is `vectorItoIntegral_isVectorMartingaleWithCovariation` with
`covMatrixProcess (killAfter) = killedCovMatrix` pointwise (unfold; `Set.indicator` cases). -/
theorem multitime_vector_martingale (hW : IsBrownianFiltration P ℱ W) {p : ℕ}
    (Φ : Fin p → ℝ → Ω → ι → ℝ) (hΦ : ∀ a, IsProgressiveL2 P ℱ (Φ a))
    (ts : Fin p → ℝ) (tq : ℝ) (hts : ∀ a, 0 ≤ ts a ∧ ts a ≤ tq) :
    (∀ a, IsProgressiveL2 P ℱ (killAfter (Φ a) (ts a))) ∧
    (∀ᵐ ω ∂P, ∀ a, ∀ τ : ℝ,
      vectorItoIntegral P ℱ W (fun a => killAfter (Φ a) (ts a)) τ ω a =
        itoIntegral P ℱ W (Φ a) (min τ (ts a)) ω) ∧
    IsVectorMartingaleWithCovariation P ℱ tq
      (vectorItoIntegral P ℱ W (fun a => killAfter (Φ a) (ts a))) (killedCovMatrix Φ ts) := by
  have hkill : ∀ a, IsProgressiveL2 P ℱ (killAfter (Φ a) (ts a)) :=
    fun a => isProgressiveL2_indicator_set P (S := Set.Iio (ts a)) measurableSet_Iio (hΦ a)
  have hcong : ∀ a, ∀ᵐ ω ∂P, ∀ τ : ℝ, itoIntegral P ℱ W (killAfter (Φ a) (ts a)) τ ω =
      itoIntegral P ℱ W (Φ a) (min τ (ts a)) ω := by
    intro a
    have h1 := itoIntegral_congr hW (hkill a) (isProgressiveL2_indicator_set P (S := Set.Ioc 0 (ts a)) measurableSet_Ioc (hΦ a))
      (fun T => sqIntegralOn_killAfter_sub_Ioc P (Φ a) (ts a) T)
    have h2 := itoIntegral_indicator_Ioc hW (hΦ a) (le_refl (0 : ℝ)) (hts a).1
    filter_upwards [h1, h2] with ω h1ω h2ω τ
    rw [h1ω τ, h2ω τ, itoIntegral_of_nonpos P ℱ W (Φ a) (min_le_right τ 0) ω, sub_zero]
  refine ⟨hkill, ?_, ?_⟩
  · filter_upwards [ae_all_iff.2 hcong] with ω hω a τ
    simp only [vectorItoIntegral, PiLp.toLp_apply]
    exact hω a τ
  · have hcov : covMatrixProcess (fun a => killAfter (Φ a) (ts a)) = killedCovMatrix Φ ts := by
      funext r ω
      ext a b
      simp only [covMatrixProcess, killedCovMatrix, Matrix.of_apply]
      by_cases h1 : r < ts a <;> by_cases h2 : r < ts b <;>
        simp [killAfter, h1, h2, lt_min_iff]
    have hvec := vectorItoIntegral_isVectorMartingaleWithCovariation hW
      (fun a => killAfter (Φ a) (ts a)) hkill tq
    rw [hcov] at hvec
    exact hvec

/-- Remark A.32 `M:B:newprob:several-times` (source lines 11037-11055): if the `a`-th statistic
contains the stochastic integral `∑_i ∫_0^{t_a} K^{a,i}_r · dB^i_r`, take `T = max_a t_a` and
`M^a_t := ∑_i ∫_0^t 1_{r < t_a} K^{a,i}_r · dB^i_r`, `Σ^{ab}_r = 1_{r<min(t_a,t_b)} ∑_i K^{a,i}_r·K^{b,i}_r`;
for independent Brownian motions `B^i` this `Σ` is precisely the quadratic covariation density
of `M` in the sense of `B:newprob:bracket` (Lemma A.27's hypothesis, represented by
`IsVectorMartingaleWithCovariation`, including `E ∫_0^T tr Σ_r dr < ∞`), and
`M^a_T = ∑_i ∫_0^{t_a} K^{a,i} · dB^i` is the original statistic.  Hence all estimates of
Appendix A.4.4 apply to joint observations, including coincident observation times (the
"constants introduce no dependence on `T`" clause is visible in the statements of
`conditional_gaussian_interpolation` and `initial_sum_martingale`, whose constants are absolute).
The Brownian family is indexed by `ι` (`ι = Fin N × Fin d` for the particle noises `(B^i)_i`,
with `K^{a,i}_r · dB^i_r = ∑_{j<d} K^{a,i,j} dB^{i,j}`). -/
theorem several_times_covariation (hW : IsBrownianFiltration P ℱ W) {p : ℕ}
    (K : Fin p → ℝ → Ω → ι → ℝ) (hK : ∀ a, IsProgressiveL2 P ℱ (K a))
    (ts : Fin p → ℝ) (hts : ∀ a, 0 ≤ ts a) (T : ℝ) (hT : ∀ a, ts a ≤ T) :
    IsVectorMartingaleWithCovariation P ℱ T
      (vectorItoIntegral P ℱ W (fun a => killAfter (K a) (ts a))) (killedCovMatrix K ts) ∧
    (∀ᵐ ω ∂P, ∀ a,
      vectorItoIntegral P ℱ W (fun a => killAfter (K a) (ts a)) T ω a =
        itoIntegral P ℱ W (K a) (ts a) ω) := by
  obtain ⟨-, hae, hvec⟩ := multitime_vector_martingale P hW K hK ts T (fun a => ⟨hts a, hT a⟩)
  refine ⟨hvec, ?_⟩
  filter_upwards [hae] with ω hω a
  rw [hω a T, min_eq_right (hT a)]

/-- A family of measurable maps into `E` gives a measurable map into the product `γ → E`
(the domain σ-algebra is taken from the hypotheses). -/
theorem hdsum_measurable_pi {α γ E : Type*} [MeasurableSpace E] {mα : MeasurableSpace α}
    (f : γ → α → E) (hf : ∀ c, Measurable (f c)) : Measurable fun x c => f c x :=
  measurable_pi_iff.2 hf

/-- Finite sums of progressive `L²` integrands are progressive `L²`. -/
theorem hdsum_isProgressiveL2_finset {β : Type*} (f : β → ℝ → Ω → ι → ℝ) (S : Finset β) :
    (∀ b ∈ S, IsProgressiveL2 P ℱ (f b)) →
      IsProgressiveL2 P ℱ (fun r ω k => ∑ b ∈ S, f b r ω k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    exact IsProgressiveL2.const P ℱ (fun _ : ι => (0 : ℝ))
  | insert c S hc ih =>
    intro hf
    have h1 := (hf c (Finset.mem_insert_self c S)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have e : (fun r ω k => ∑ b ∈ insert c S, f b r ω k) =
        (fun s ω => f c s ω + fun k => ∑ b ∈ S, f b s ω k) := by
      funext r ω k
      simp [Finset.sum_insert hc]
    rw [e]
    exact h1

/-- Itô integrals of finite sums of integrands are the sums of the Itô integrals (a.e., for all
times). -/
theorem hdsum_itoIntegral_finset_ae {β : Type*} (hW : IsBrownianFiltration P ℱ W)
    (f : β → ℝ → Ω → ι → ℝ) (S : Finset β) :
    (∀ b ∈ S, IsProgressiveL2 P ℱ (f b)) →
      ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun r ω k => ∑ b ∈ S, f b r ω k) t ω =
        ∑ b ∈ S, itoIntegral P ℱ W (f b) t ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _
    filter_upwards [itoIntegral_const hW (fun _ : ι => (0 : ℝ))] with ω hω t
    simpa using hω t
  | insert c S hc ih =>
    intro hf
    have hS := hdsum_isProgressiveL2_finset P f S (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have h1 := itoIntegral_add hW (hf c (Finset.mem_insert_self c S)) hS
    filter_upwards [h1, ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))] with ω h1ω h2ω t
    have e : (fun r ω k => ∑ b ∈ insert c S, f b r ω k) =
        (fun s ω => f c s ω + fun k => ∑ b ∈ S, f b s ω k) := by
      funext r ω k
      simp [Finset.sum_insert hc]
    rw [e, Finset.sum_insert hc]
    exact (h1ω t).trans (by rw [h2ω t])

/-- Pointwise Cauchy–Schwarz for finite sums of `ℝ≥0∞`-valued squared norms. -/
theorem hdsum_enorm_sq_finset_le {E γ : Type*} [NormedAddCommGroup E] (S : Finset γ) (d : γ → E) :
    ‖∑ a ∈ S, d a‖ₑ ^ 2 ≤ ((S.card : ℕ) : ℝ≥0∞) * ∑ a ∈ S, ‖d a‖ₑ ^ 2 := by
  calc ‖∑ a ∈ S, d a‖ₑ ^ 2 = ENNReal.ofReal (‖∑ a ∈ S, d a‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ ≤ ENNReal.ofReal ((S.card : ℝ) * ∑ a ∈ S, ‖d a‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2)
          sq_sum_le_card_mul_sum_sq)
    _ = ((S.card : ℕ) : ℝ≥0∞) * ∑ a ∈ S, ‖d a‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
        congr 1
        exact Finset.sum_congr rfl fun a _ => by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The squared `ℝ≥0∞`-norm of a finite `PiLp 2` vector is the sum of the squared coordinates. -/
theorem hdsum_enorm_sq_toLp {q : ℕ} {E : Type*} [NormedAddCommGroup E] (v : Fin q → E) :
    ‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin q => E)‖ₑ ^ 2 = ∑ a, ‖v a‖ₑ ^ 2 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin q => E) (WithLp.toLp 2 v)
  simp only [PiLp.toLp_apply] at h
  calc ‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin q => E)‖ₑ ^ 2
      = ENNReal.ofReal (‖(WithLp.toLp 2 v : PiLp 2 fun _ : Fin q => E)‖ ^ 2) := by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (∑ a, ‖v a‖ ^ 2) := by rw [h]
    _ = ∑ a, ENNReal.ofReal (‖v a‖ ^ 2) := ENNReal.ofReal_sum_of_nonneg fun a _ => sq_nonneg _
    _ = ∑ a, ‖v a‖ₑ ^ 2 := Finset.sum_congr rfl fun a _ => by
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Joint measurability of the clamped squared norm sum of a progressive family. -/
theorem hdsum_measurable_tsum {κ : Type*} [Countable κ] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Φ : ℝ → Ω → κ → E)
    (hΦ : ∀ k, IsProgressive ℱ (fun r ω => Φ r ω k)) (T : ℝ) :
    Measurable (fun p : ℝ × Ω => ∑' k, ‖Φ (min p.1 T) p.2 k‖ₑ ^ 2) :=
  Measurable.ennreal_tsum fun k => ((measurable_clamp (hΦ k) T).enorm).pow_const 2

/-- The `L²` size `ω ↦ ∫_0^T ∑_k ‖Φ_r ω k‖²` of a progressive family is measurable. -/
theorem hdsum_measurable_hsSq {κ : Type*} [Countable κ] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (Φ : ℝ → Ω → κ → E)
    (hΦ : ∀ k, IsProgressive ℱ (fun r ω => Φ r ω k)) (T : ℝ) :
    Measurable (fun ω => ∫⁻ r in Set.Icc 0 T, ∑' k, ‖Φ r ω k‖ₑ ^ 2) := by
  have e : (fun ω => ∫⁻ r in Set.Icc 0 T, ∑' k, ‖Φ r ω k‖ₑ ^ 2) =
      fun ω => ∫⁻ r in Set.Icc 0 T, ∑' k, ‖Φ (min r T) ω k‖ₑ ^ 2 := by
    funext ω
    exact setLIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [min_eq_left hr.2])
  rw [e]
  exact (hdsum_measurable_tsum Φ hΦ T).lintegral_prod_left' (μ := volume.restrict (Set.Icc 0 T))

/-- A coordinate of a progressive `L²` integrand, paired with a fixed vector `x`, is a progressive
`L²` integrand on every finite set of indices. -/
theorem hdsum_isProgressiveL2_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {κ : Type*} (Φ : ℝ → Ω → κ → H)
    (hΦ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ) (x : H) (S : Finset κ) :
    IsProgressiveL2 P ℱ (fun r ω (k : S) => inner ℝ (Φ r ω k) x) := by
  have hc : Measurable fun v : H => inner ℝ v x :=
    (continuous_id.inner continuous_const).measurable
  have hx : ‖x‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
  have hsq1 : ∀ v : H, ‖inner ℝ v x‖ₑ ^ 2 ≤ ‖x‖ₑ ^ 2 * ‖v‖ₑ ^ 2 := by
    intro v
    have h : ‖inner ℝ v x‖ ≤ ‖v‖ * ‖x‖ := norm_inner_le_norm v x
    calc ‖inner ℝ v x‖ₑ ^ 2 = ENNReal.ofReal (‖inner ℝ v x‖ ^ 2) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ ENNReal.ofReal ((‖v‖ * ‖x‖) ^ 2) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)
      _ = ‖x‖ₑ ^ 2 * ‖v‖ₑ ^ 2 := by
          rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
            ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ofReal_norm]
          ring
  have hpt : ∀ r ω, ∑ k : S, ‖inner ℝ (Φ r ω k) x‖ₑ ^ 2 ≤
      ‖x‖ₑ ^ 2 * ∑' k, ‖Φ r ω k‖ₑ ^ 2 := by
    intro r ω
    calc ∑ k : S, ‖inner ℝ (Φ r ω k) x‖ₑ ^ 2 ≤ ∑ k : S, ‖x‖ₑ ^ 2 * ‖Φ r ω k‖ₑ ^ 2 :=
          Finset.sum_le_sum fun k _ => hsq1 _
      _ = ‖x‖ₑ ^ 2 * ∑ k ∈ S, ‖Φ r ω k‖ₑ ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_coe_sort S (fun k => ‖Φ r ω k‖ₑ ^ 2)
      _ ≤ ‖x‖ₑ ^ 2 * ∑' k, ‖Φ r ω k‖ₑ ^ 2 := mul_le_mul_of_nonneg_left (ENNReal.sum_le_tsum S) zero_le
  refine ⟨fun i => hdsum_measurable_pi (fun (k : S) (p : Set.Iic i × Ω) => inner ℝ (Φ p.1 p.2 k) x)
    fun k => hc.comp ((hΦ 0).prog k i), fun T => ?_⟩
  have hle : sqIntegralOn P (fun r ω (k : S) => inner ℝ (Φ r ω k) x) T ≤
      ‖x‖ₑ ^ 2 * hsSqIntegralOn P Φ T := by
    calc sqIntegralOn P (fun r ω (k : S) => inner ℝ (Φ r ω k) x) T
        ≤ ∫⁻ ω, (∫⁻ r in Set.Icc 0 T, ‖x‖ₑ ^ 2 * ∑' k, ‖Φ r ω k‖ₑ ^ 2) ∂P :=
          lintegral_mono fun ω => lintegral_mono fun r => hpt r ω
      _ = ∫⁻ ω, ‖x‖ₑ ^ 2 * (∫⁻ r in Set.Icc 0 T, ∑' k, ‖Φ r ω k‖ₑ ^ 2) ∂P :=
          lintegral_congr fun ω => lintegral_const_mul' _ _ hx
      _ = ‖x‖ₑ ^ 2 * hsSqIntegralOn P Φ T := lintegral_const_mul' _ _ hx
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hx) (hΦ T).sq)

/-- The `L²` size of the Hilbert direct sum of integrands is at most the sum of the `L²` sizes. -/
theorem hdsum_hsSq_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {κ : Type*} [Countable κ] {q : ℕ} (Φ : Fin q → ℝ → Ω → κ → H)
    (hΦ : ∀ a, ∀ T : ℝ, IsHSIntegrand P ℱ T (Φ a)) (t : ℝ) :
    hsSqIntegralOn P (fun r ω k => (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)) t
      ≤ ∑ a, hsSqIntegralOn P (Φ a) t := by
  refine le_of_eq ?_
  have htsum : ∀ r ω, ∑' k, ∑ a, ‖Φ a r ω k‖ₑ ^ 2 = ∑ a, ∑' k, ‖Φ a r ω k‖ₑ ^ 2 :=
    fun r ω => Summable.tsum_finsetSum fun a _ => ENNReal.summable
  have hmeasG : ∀ (a : Fin q) (ω : Ω), Measurable fun r : ℝ => ∑' k, ‖Φ a (min r t) ω k‖ₑ ^ 2 :=
    fun a ω => (hdsum_measurable_tsum (Φ a) (fun k => (hΦ a t).prog k) t).comp
      (measurable_id.prodMk measurable_const)
  have hpt : ∀ ω : Ω, ∫⁻ r in Set.Icc 0 t,
      ∑' k, ‖(WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)‖ₑ ^ 2
        = ∑ a, ∫⁻ r in Set.Icc 0 t, ∑' k, ‖Φ a r ω k‖ₑ ^ 2 := by
    intro ω
    have hpw : ∀ r : ℝ, ∑' k, ‖(WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)‖ₑ ^ 2
        = ∑ a, ∑' k, ‖Φ a r ω k‖ₑ ^ 2 := by
      intro r
      simp only [hdsum_enorm_sq_toLp]
      exact htsum r ω
    calc ∫⁻ r in Set.Icc 0 t,
          ∑' k, ‖(WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)‖ₑ ^ 2
        = ∫⁻ r in Set.Icc 0 t, ∑ a, ∑' k, ‖Φ a r ω k‖ₑ ^ 2 := lintegral_congr fun r => hpw r
      _ = ∫⁻ r in Set.Icc 0 t, ∑ a, ∑' k, ‖Φ a (min r t) ω k‖ₑ ^ 2 :=
          setLIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [min_eq_left hr.2])
      _ = ∑ a, ∫⁻ r in Set.Icc 0 t, ∑' k, ‖Φ a (min r t) ω k‖ₑ ^ 2 :=
          lintegral_finsetSum _ (fun a _ => hmeasG a ω)
      _ = ∑ a, ∫⁻ r in Set.Icc 0 t, ∑' k, ‖Φ a r ω k‖ₑ ^ 2 :=
          Finset.sum_congr rfl fun a _ =>
            setLIntegral_congr_fun measurableSet_Icc (fun r hr => by simp only [min_eq_left hr.2])
  calc hsSqIntegralOn P (fun r ω k => (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)) t
      = ∫⁻ ω, ∑ a, (∫⁻ r in Set.Icc 0 t, ∑' k, ‖Φ a r ω k‖ₑ ^ 2) ∂P := lintegral_congr hpt
    _ = ∑ a, ∫⁻ ω, (∫⁻ r in Set.Icc 0 t, ∑' k, ‖Φ a r ω k‖ₑ ^ 2) ∂P :=
        lintegral_finsetSum _ fun a _ => hdsum_measurable_hsSq (Φ a) (fun k => (hΦ a t).prog k) t
    _ = ∑ a, hsSqIntegralOn P (Φ a) t := rfl

/-- Remark A.25 `M:B:rem:clt-complex` (source lines 10698-10700), the Hilbert-valued clause:
finitely many `H`-valued terminal fields fit the single-field statements by taking the finite
Hilbert direct sum `⨁_{a<q} H = PiLp 2 (fun _ : Fin q => H)`: if `M_a = ∫ Φ_a dW` are `H`-valued
Itô integrals, the direct-sum process `(M_a)_a` is the `⨁ H`-valued Itô integral of the direct-sum
integrand `(Φ_a)_a`, and the direct-sum integrand is Hilbert–Schmidt when each `Φ_a` is (its
`𝓛₂` norm squared is the sum).  Combined with `multitime_vector_martingale` (integrands killed
after the observation times) this realises statistics of several `H`-valued fields at several
times as one terminal value, to which `hilbert_polar_coupling`/`hilbert_martingale_w2` apply as
stated.  The complex clause ("a `ℂ^p`-valued martingale is an `ℝ^{2p}`-valued one") has no
content beyond the real-linear isometry `ℂ^p ≅ ℝ^{2p}` (Mathlib `Complex.orthonormalBasisOneI`,
`Complex.equivRealProdCLM`), under which laws, `d_{C²}` and `W_p` are preserved; it is recorded in
`coverage.tsv` as such.

PLAN: unfold both predicates; the coordinate functional `⟨(M_a)_a, (x_a)_a⟩ = ∑_a ⟨M_a, x_a⟩` is a
finite sum of the coordinate limits (`itoIntegral_add` for the finite sum of integrands, and
`Tendsto.add` for the `L²` limits along `Finset κ`); continuity/adaptedness/zero are
componentwise (`PiLp.continuous_toLp`, `measurable_pi_iff`); the Hilbert–Schmidt bound is
`∑' k, ∑_a ‖Φ_a k‖² = ∑_a ∑' k ‖Φ_a k‖²` (`ENNReal.tsum_finsetSum`-type lemmas). -/
theorem hilbert_direct_sum_ito {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {κ : Type*} [Countable κ] (W' : ℝ≥0 → Ω → κ → ℝ) (hW' : IsCylindricalBrownian P ℱ W')
    (t : ℝ) {q : ℕ} (Φ : Fin q → ℝ → Ω → κ → H) (hΦ : ∀ a, ∀ T : ℝ, IsHSIntegrand P ℱ T (Φ a))
    (M : Fin q → ℝ → Ω → H) (hM : ∀ a, IsHilbertItoIntegral P ℱ W' (Φ a) (M a)) :
    IsHSIntegrand P ℱ t (fun r ω k => (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)) ∧
    IsHilbertItoIntegral P ℱ W'
      (fun r ω k => (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H))
      (fun τ ω => (WithLp.toLp 2 fun a => M a τ ω : PiLp 2 fun _ : Fin q => H)) := by
  have hΨprog : ∀ k, IsProgressive ℱ
      (fun r ω => (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)) := by
    intro k i
    exact (WithLp.measurable_toLp 2 _).comp (hdsum_measurable_pi _ fun a => (hΦ a t).prog k i)
  have hΨsum : ∀ r ω, Summable fun k =>
      ‖(WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H)‖ ^ 2 := by
    intro r ω
    simp only [PiLp.norm_sq_eq_of_L2 (fun _ : Fin q => H)]
    exact summable_sum fun a _ => (hΦ a t).summable r ω
  refine ⟨⟨hΨprog, hΨsum, lt_of_le_of_lt (hdsum_hsSq_le P Φ hΦ t)
    (ENNReal.sum_lt_top.2 fun a _ => (hΦ a t).sq)⟩, ?_⟩
  refine
    { cont := ?_, adapted := ?_, zero := ?_, approx := ?_ }
  · intro ω
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun a => (hM a).cont ω)
  · intro i
    exact (WithLp.measurable_toLp 2 _).comp (hdsum_measurable_pi _ fun a => (hM a).adapted i)
  · intro τ hτ ω
    have h0 : ∀ a, M a τ ω = 0 := fun a => (hM a).zero τ hτ ω
    simp [h0]
    rfl
  · intro τ hτ x
    have hinnerM : ∀ ω, inner ℝ (WithLp.toLp 2 fun a => M a τ ω : PiLp 2 fun _ : Fin q => H) x
        = ∑ a, inner ℝ (M a τ ω) (x a) := by
      intro ω
      simp [PiLp.inner_apply]
    -- pointwise decomposition of the finite-index Itô integral
    have hae : ∀ s : Finset κ, ∀ᵐ ω ∂P,
        itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
          (fun r ω (k : s) => inner ℝ (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H) x)
          τ ω =
        ∑ a, itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
          (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω := by
      intro s
      have h := hdsum_itoIntegral_finset_ae P (hW' s)
        (fun a (r : ℝ) (ω : Ω) (k : s) => inner ℝ (Φ a r ω k) (x a)) Finset.univ
        (fun a _ => hdsum_isProgressiveL2_inner P (Φ a) (hΦ a) (x a) s)
      filter_upwards [h] with ω hω
      have e : (fun r ω (k : s) =>
          inner ℝ (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H) x) =
          fun r ω (k : s) => ∑ a ∈ Finset.univ, inner ℝ (Φ a r ω k) (x a) := by
        funext r ω k
        simp [PiLp.inner_apply]
      rw [e]
      exact hω τ
    have hmeas : ∀ s : Finset κ, ∀ a : Fin q, Measurable fun ω =>
        ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
            (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω - inner ℝ (M a τ ω) (x a)‖ₑ ^ 2 := by
      intro s a
      have h1 : Measurable fun ω => itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
          (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω :=
        (adapted_itoIntegral P ℱ _ _ τ).mono (ℱ.le τ) le_rfl
      have h2 : Measurable fun ω => inner ℝ (M a τ ω) (x a) :=
        (continuous_id.inner continuous_const).measurable.comp
          (((hM a).adapted τ).mono (ℱ.le τ) le_rfl)
      exact ((h1.sub h2).enorm).pow_const 2
    have hbound : ∀ s : Finset κ,
        ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
            (fun r ω (k : s) => inner ℝ (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H) x)
            τ ω - inner ℝ (WithLp.toLp 2 fun a => M a τ ω : PiLp 2 fun _ : Fin q => H) x‖ₑ ^ 2 ∂P
        ≤ ((Finset.univ : Finset (Fin q)).card : ℝ≥0∞) * ∑ a : Fin q,
          ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
            (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω - inner ℝ (M a τ ω) (x a)‖ₑ ^ 2 ∂P := by
      intro s
      calc ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
            (fun r ω (k : s) => inner ℝ (WithLp.toLp 2 fun a => Φ a r ω k : PiLp 2 fun _ : Fin q => H) x)
            τ ω - inner ℝ (WithLp.toLp 2 fun a => M a τ ω : PiLp 2 fun _ : Fin q => H) x‖ₑ ^ 2 ∂P
          = ∫⁻ ω, ‖∑ a : Fin q, (itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
              (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω - inner ℝ (M a τ ω) (x a))‖ₑ ^ 2 ∂P := by
            refine lintegral_congr_ae ?_
            filter_upwards [hae s] with ω hω
            rw [hω, hinnerM ω, Finset.sum_sub_distrib]
        _ ≤ ∫⁻ ω, ((Finset.univ : Finset (Fin q)).card : ℝ≥0∞) * ∑ a : Fin q,
              ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
                (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω - inner ℝ (M a τ ω) (x a)‖ₑ ^ 2 ∂P :=
            lintegral_mono fun ω => hdsum_enorm_sq_finset_le _ _
        _ = ((Finset.univ : Finset (Fin q)).card : ℝ≥0∞) * ∑ a : Fin q,
              ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
                (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω - inner ℝ (M a τ ω) (x a)‖ₑ ^ 2 ∂P := by
            rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
              lintegral_finsetSum _ (fun a _ => hmeas s a)]
    have hlim : Tendsto (fun s : Finset κ => ((Finset.univ : Finset (Fin q)).card : ℝ≥0∞) * ∑ a : Fin q,
          ∫⁻ ω, ‖itoIntegral P ℱ (fun t ω (k : s) => W' t ω k)
            (fun r ω (k : s) => inner ℝ (Φ a r ω k) (x a)) τ ω - inner ℝ (M a τ ω) (x a)‖ₑ ^ 2 ∂P)
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ((Finset.univ : Finset (Fin q)).card : ℝ≥0∞))
        (tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun a _ => (hM a).approx τ hτ (x a)))
        (Or.inr (ENNReal.natCast_ne_top _))
      rwa [Finset.sum_const_zero, mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun s => zero_le) hbound

end MultiTime

/-! ### Appendix A.4.4: Gaussian approximation with random initial data -/

section RandomInitial

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The test class of `B:newprob:metric` (source lines 10763-10773): `h ∈ C_b^3(ℝ^p)` with
`max_{1≤j≤3} sup_x ‖D^j h(x)‖_op ≤ 1` (`C_b^3`: `h` and its derivatives through order `3` continuous
and bounded; the MAX is over the orders `1, 2, 3` only). -/
def D3TestClass (p : ℕ) : Set ((ℝ^p) → ℝ) :=
  {h | MemCb 3 h ∧ ∀ j, 1 ≤ j → j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j h x‖ ≤ 1}

/-- The metric `𝖽₃(U,V) = sup { |E h(U) - E h(V)| : h ∈ D3TestClass }` of `B:newprob:metric`,
on laws, in `ℝ≥0∞` (the supremum is infinite when the laws have no first moment; a real `iSup`
would then be the junk value `0`). -/
def d3DistE (μ ν : Measure (ℝ^p)) : ℝ≥0∞ :=
  ⨆ h : D3TestClass p, ENNReal.ofReal |∫ x, h.1 x ∂μ - ∫ x, h.1 x ∂ν|

/-- `sup_x ‖D²h(x)‖_op` (a genuine supremum for `h ∈ C_b^2`). -/
def hessSup (h : (ℝ^p) → ℝ) : ℝ := ⨆ x, ‖iteratedFDeriv ℝ 2 h x‖

/-- The trace-norm discrepancy `E ∫_0^T ‖Σ_r - Σ̄_r‖_{S_1} dr` of the finite-dimensional
statements (`B:newprob:conditional-bound` and following). -/
def covDiscrepancyMatrix (T : ℝ) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∫ ω, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P

/-- The integrated deterministic covariance `∫_0^T Σ̄_r dr` (entrywise). -/
def integratedCov (T : ℝ) (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => ∫ σ in Set.Icc 0 T, sb σ i j

/-- The hypotheses on the deterministic coefficient `Σ̄ : [0,T] → ℝ^{p×p}` of Lemma A.27
(lines 10797-10798): measurable, symmetric nonnegative, integrable. -/
structure IsDetCovMatrix (T : ℝ) (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) : Prop where
  meas : Measurable sb
  psd : ∀ σ ∈ Set.Icc 0 T, (sb σ).PosSemidef
  int : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 T)

/-! ### Route for Lemma A.27 (as formalised)

Not by Itô's formula: the unconditional bound `multivariate_martingale_clt` (Lemma A.21) is applied
under `P[· | B]` for `B ∈ ℱ_0` (`isVec_cond`), to the translate `y ↦ h(x + y)` (same Hessian
bound), which handles an `ℱ_0`-measurable shift `X` with finitely many values (`shift_bound_simple`,
the independence of `G` from `ℱ_T ⊇ ℱ_0` identifying `∫_B h(x+G) = P(B) ∫ h(x+·) dγ`).  A general
`X` is approximated pointwise by `ℱ_0`-simple functions (`StronglyMeasurable.approx`), with
dominated convergence for the bounded continuous `h` (`shift_bound`).  The a.s. inequality for the
conditional expectations follows from the inequality on all `ℱ_0`-sets
(`ae_le_of_setIntegral_le_trim`). -/

section A27Aux

omit [IsProbabilityMeasure P] in
lemma setIntegral_fiber_sum {β : Type*} [DecidableEq β] {A : Set Ω} (hA : MeasurableSet A)
    (S : Finset β) (ξ : Ω → β) (hS : ∀ ω, ξ ω ∈ S) (hξ : ∀ x, MeasurableSet (ξ ⁻¹' {x}))
    {F : Ω → ℝ} (hF : Integrable F P) :
    ∫ ω in A, F ω ∂P = ∑ x ∈ S, ∫ ω in A ∩ ξ ⁻¹' {x}, F ω ∂P := by
  have hU : A = ⋃ x ∈ S, (A ∩ ξ ⁻¹' {x}) := by
    ext ω; simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      exists_prop]
    exact ⟨fun h => ⟨ξ ω, hS ω, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩
  conv_lhs => rw [hU]
  refine integral_biUnion_finset S (fun x _ => hA.inter (hξ x)) ?_ (fun x _ => hF.integrableOn)
  intro x _ y _ hxy
  refine Set.disjoint_left.2 fun ω h1 h2 => hxy ?_
  have h3 := h1.2
  have h4 := h2.2
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at h3 h4
  rw [← h3, ← h4]

lemma isVec_cond {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → (ℝ^p)}
    {Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ} (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) (hP0 : P A ≠ 0) :
    IsVectorMartingaleWithCovariation (ProbabilityTheory.cond P A) ℱ T M Sg := by
  have hac : ProbabilityTheory.cond P A ≪ P := ProbabilityTheory.cond_absolutelyContinuous
  have hc : (P A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hP0
  have hzero : ∀ a : Fin p, (fun ω => M 0 ω a) =ᵐ[P] 0 := fun a => by
    filter_upwards [hM.zero] with ω h
    simp [h]
  refine
    { martingale := fun a => martingale_cond P (hM.martingale a) (hzero a) hA hP0
      zero := hac.ae_le hM.zero
      cont := hac.ae_le hM.cont
      sq_int := fun τ hτ => ?_
      sigma_meas := hM.sigma_meas
      sigma_adapted := hM.sigma_adapted
      sigma_psd := hac.ae_le hM.sigma_psd
      sigma_int := ?_
      sigma_pathint := hac.ae_le hM.sigma_pathint
      sigma_entry_int := hac.ae_le hM.sigma_entry_int
      covariation := fun a b => ?_ }
  · exact ((hM.sq_int τ hτ).restrict A).smul_measure hc
  · exact (hM.sigma_int.restrict (s := A)).smul_measure hc
  · refine martingale_cond P (hM.covariation a b) ?_ hA hP0
    filter_upwards [hM.zero] with ω h
    simp [h]

lemma const_shift_bound (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (h : (ℝ^p) → ℝ) (hh : MemCb 2 h) (x : ℝ^p) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    |(∫ ω in A, h (x + M T ω) ∂P) -
        P.real A * ∫ z, h (x + z) ∂(multivariateGaussian 0 (integratedCov T sb))| ≤
      (1 / 2) * hessSup h * ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  have hAm : MeasurableSet A := ℱ.le 0 _ hA
  by_cases hP0 : P A = 0
  · have : P.restrict A = 0 := Measure.restrict_eq_zero.2 hP0
    simp [this, Measure.real, hP0]
  · have : IsProbabilityMeasure (ProbabilityTheory.cond P A) :=
      ProbabilityTheory.cond_isProbabilityMeasure hP0
    have hMc := isVec_cond P hM hA hP0
    have hhx : ContDiff ℝ 2 (fun y => h (x + y)) := hh.1.comp (contDiff_const.add contDiff_id)
    have hH : ∀ y, ‖iteratedFDeriv ℝ 2 (fun y => h (x + y)) y‖ ≤ hessSup h := by
      intro y
      rw [iteratedFDeriv_comp_add_left]
      exact le_ciSup (hh.2 2 le_rfl) (x + y)
    have hbdd : BddAbove (Set.range fun y => ‖iteratedFDeriv ℝ 2 (fun y => h (x + y)) y‖) :=
      ⟨hessSup h, by rintro _ ⟨y, rfl⟩; exact hH y⟩
    have hsup : (⨆ y, ‖iteratedFDeriv ℝ 2 (fun y => h (x + y)) y‖) ≤ hessSup h :=
      ciSup_le hH
    have hcore := multivariate_martingale_clt (ProbabilityTheory.cond P A) ℱ T hT M Sg hMc sb
      hsb.meas hsb.int hsb.psd (fun y => h (x + y)) hhx hbdd
    have hI : ∀ F : Ω → ℝ, ∫ ω, F ω ∂(ProbabilityTheory.cond P A) =
        ((P A).toReal)⁻¹ * ∫ ω in A, F ω ∂P := by
      intro F
      simp [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    rw [hI, hI] at hcore
    have hp : 0 < (P A).toReal := ENNReal.toReal_pos hP0 (measure_ne_top P A)
    have hpr : P.real A = (P A).toReal := rfl
    have hJ0 : 0 ≤ ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P :=
      setIntegral_nonneg hAm fun ω _ =>
        setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
    have hH0 : 0 ≤ hessSup h := (norm_nonneg _).trans (hH 0)
    rw [hpr]
    set c := ∫ z, h (x + z) ∂(multivariateGaussian 0 (integratedCov T sb)) with hc
    set a := ∫ ω in A, h (x + M T ω) ∂P with ha
    set J := ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P with hJ
    have e1 : a - (P A).toReal * c = (P A).toReal * (((P A).toReal)⁻¹ * a - c) := by
      field_simp
    rw [e1, abs_mul, abs_of_pos hp]
    have hcore' : |((P A).toReal)⁻¹ * a - c| ≤ (1 / 2) * hessSup h * (((P A).toReal)⁻¹ * J) := by
      refine hcore.trans ?_
      have : 0 ≤ ((P A).toReal)⁻¹ * J := by positivity
      calc _ ≤ (1 / 2) * hessSup h * (((P A).toReal)⁻¹ * J) := by
            rw [mul_assoc, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsup this) (by norm_num)
        _ = _ := by ring
    calc (P A).toReal * |((P A).toReal)⁻¹ * a - c|
        ≤ (P A).toReal * ((1 / 2) * hessSup h * (((P A).toReal)⁻¹ * J)) :=
          mul_le_mul_of_nonneg_left hcore' hp.le
      _ = _ := by field_simp

lemma memCb_bound {h : (ℝ^p) → ℝ} (hh : MemCb 2 h) : ∃ C, ∀ x, |h x| ≤ C := by
  obtain ⟨C, hC⟩ := hh.2 0 (Nat.zero_le _)
  exact ⟨C, fun x => by
    have := hC ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this⟩

omit [IsProbabilityMeasure P] in
lemma integrable_memCb_comp {h : (ℝ^p) → ℝ} (hh : MemCb 2 h) {f : Ω → (ℝ^p)}
    (hf : AEMeasurable f P) [IsFiniteMeasure P] : Integrable (fun ω => h (f ω)) P := by
  obtain ⟨C, hC⟩ := memCb_bound hh
  exact Integrable.of_bound (C := C)
    (hh.1.continuous.measurable.comp_aemeasurable hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by simpa using hC (f ω))

lemma setIntegral_indep_comp {ℱ : Filtration ℝ mΩ} {T : ℝ} (hT : 0 ≤ T) {G : Ω → (ℝ^p)}
    (hGm : AEMeasurable G P)
    (hGind : Indep (MeasurableSpace.comap G inferInstance) (ℱ T) P) {φ : (ℝ^p) → ℝ}
    (hφ : Continuous φ) {B : Set Ω} (hB : MeasurableSet[ℱ T] B) :
    ∫ ω in B, φ (G ω) ∂P = P.real B * ∫ z, φ z ∂(law P G) := by
  have hBm : MeasurableSet B := ℱ.le T _ hB
  have hind : IndepFun (B.indicator (fun _ => (1 : ℝ))) (fun ω => φ (G ω)) P := by
    unfold IndepFun
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hGind.symm ?_) ?_
    · exact (measurable_const.indicator (m := ℱ T) hB).comap_le
    · rw [show (fun ω => φ (G ω)) = φ ∘ G from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hφ.measurable.comap_le
  have hX : AEStronglyMeasurable (B.indicator (fun _ => (1 : ℝ))) P :=
    (measurable_const.indicator hBm).aestronglyMeasurable
  have hY : AEStronglyMeasurable (fun ω => φ (G ω)) P :=
    (hφ.measurable.comp_aemeasurable hGm).aestronglyMeasurable
  have h1 := hind.integral_fun_mul_eq_mul_integral hX hY
  have e1 : ∫ ω in B, φ (G ω) ∂P = ∫ ω, B.indicator (fun _ => (1 : ℝ)) ω * φ (G ω) ∂P := by
    rw [← integral_indicator hBm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ B <;> simp [hω]
  rw [e1, h1]
  congr 1
  · rw [integral_indicator_const _ hBm]; simp [Measure.real]
  · exact (integral_map hGm hφ.aestronglyMeasurable).symm

lemma shift_bound_simple (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (ξ : Ω → (ℝ^p)) (S : Finset (ℝ^p)) (hS : ∀ ω, ξ ω ∈ S)
    (hξ : ∀ x, MeasurableSet[ℱ 0] (ξ ⁻¹' {x}))
    (G : Ω → (ℝ^p)) (hGm : AEMeasurable G P)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb))
    (hGind : Indep (MeasurableSpace.comap G inferInstance) (ℱ T) P)
    (h : (ℝ^p) → ℝ) (hh : MemCb 2 h) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    |(∫ ω in A, h (ξ ω + M T ω) ∂P) - ∫ ω in A, h (ξ ω + G ω) ∂P| ≤
      (1 / 2) * hessSup h * ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  have hm0 : ∀ B, MeasurableSet[ℱ 0] B → MeasurableSet B := fun B hB => ℱ.le 0 _ hB
  have hξm : ∀ x, MeasurableSet (ξ ⁻¹' {x}) := fun x => hm0 _ (hξ x)
  have hξmeas : Measurable ξ := by
    intro s _
    have : ξ ⁻¹' s = ⋃ x ∈ (S.filter (· ∈ s)), ξ ⁻¹' {x} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
        Finset.mem_filter]
      exact ⟨fun h => ⟨ξ ω, ⟨hS ω, h⟩, rfl⟩, fun ⟨x, ⟨_, hx⟩, e⟩ => e ▸ hx⟩
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => hξm x
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hint1 : Integrable (fun ω => h (ξ ω + M T ω)) P :=
    integrable_memCb_comp P hh (hξmeas.aemeasurable.add hMt)
  have hint2 : Integrable (fun ω => h (ξ ω + G ω)) P :=
    integrable_memCb_comp P hh (hξmeas.aemeasurable.add hGm)
  have hintg : Integrable (fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) P :=
    LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  rw [setIntegral_fiber_sum P (hm0 A hA) S ξ hS hξm hint1,
    setIntegral_fiber_sum P (hm0 A hA) S ξ hS hξm hint2,
    setIntegral_fiber_sum P (hm0 A hA) S ξ hS hξm hintg, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have hB : MeasurableSet[ℱ 0] (A ∩ ξ ⁻¹' {x}) := hA.inter (hξ x)
  have hBm := hm0 _ hB
  have e1 : ∫ ω in A ∩ ξ ⁻¹' {x}, h (ξ ω + M T ω) ∂P = ∫ ω in A ∩ ξ ⁻¹' {x}, h (x + M T ω) ∂P :=
    setIntegral_congr_fun hBm fun ω hω => by rw [show ξ ω = x from hω.2]
  have e2 : ∫ ω in A ∩ ξ ⁻¹' {x}, h (ξ ω + G ω) ∂P = ∫ ω in A ∩ ξ ⁻¹' {x}, h (x + G ω) ∂P :=
    setIntegral_congr_fun hBm fun ω hω => by rw [show ξ ω = x from hω.2]
  have e3 : ∫ ω in A ∩ ξ ⁻¹' {x}, h (x + G ω) ∂P =
      P.real (A ∩ ξ ⁻¹' {x}) * ∫ z, h (x + z) ∂(multivariateGaussian 0 (integratedCov T sb)) := by
    rw [setIntegral_indep_comp P hT hGm hGind (φ := fun z => h (x + z))
      (hh.1.continuous.comp (continuous_const.add continuous_id)) (ℱ.mono hT _ hB), hG]
  rw [e1, e2, e3]
  exact const_shift_bound P ℱ T hT M Sg hM sb hsb h hh x hB

omit [IsProbabilityMeasure P] in
lemma exists_finrange_approx_a27 {m : MeasurableSpace Ω} {X : Ω → (ℝ^p)} (hX : Measurable[m] X) :
    ∃ (ξ : ℕ → Ω → (ℝ^p)) (S : ℕ → Finset (ℝ^p)), (∀ n ω, ξ n ω ∈ S n) ∧
      (∀ n x, MeasurableSet[m] (ξ n ⁻¹' {x})) ∧ (∀ n, Measurable[m] (ξ n)) ∧
      ∀ ω, Tendsto (fun n => ξ n ω) atTop (𝓝 (X ω)) := by
  classical
  have hXs : StronglyMeasurable[m] X := hX.stronglyMeasurable
  exact ⟨fun n => hXs.approx n, fun n => (hXs.approx n).range,
    fun n ω => SimpleFunc.mem_range_self _ ω, fun n x => (hXs.approx n).measurableSet_fiber x,
    fun n => (hXs.approx n).measurable, fun ω => hXs.tendsto_approx ω⟩

lemma shift_bound (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (X : Ω → (ℝ^p)) (hX : Measurable[ℱ 0] X)
    (G : Ω → (ℝ^p)) (hGm : AEMeasurable G P)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb))
    (hGind : Indep (MeasurableSpace.comap G inferInstance) (ℱ T) P)
    (h : (ℝ^p) → ℝ) (hh : MemCb 2 h) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    |(∫ ω in A, h (X ω + M T ω) ∂P) - ∫ ω in A, h (X ω + G ω) ∂P| ≤
      (1 / 2) * hessSup h * ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  obtain ⟨ξ, S, hS, hξ, hξm0, hξt⟩ := exists_finrange_approx_a27 (m := ℱ 0) hX
  have hm0 : ∀ B, MeasurableSet[ℱ 0] B → MeasurableSet B := fun B hB => ℱ.le 0 _ hB
  have hAm := hm0 A hA
  have hξm : ∀ n, Measurable (ξ n) := fun n => (hξm0 n).mono (ℱ.le 0) le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  obtain ⟨C, hC⟩ := memCb_bound hh
  have hbd : ∀ (f : Ω → (ℝ^p)), AEMeasurable f P →
      Tendsto (fun n => ∫ ω in A, h (ξ n ω + f ω) ∂P) atTop (𝓝 (∫ ω in A, h (X ω + f ω) ∂P)) := by
    intro f hf
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
      (integrable_const C) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (integrable_memCb_comp (P.restrict A) hh
        ((hξm n).aemeasurable.add hf.restrict)).aestronglyMeasurable
    · simpa using hC _
    · exact (hh.1.continuous.tendsto _).comp ((hξt ω).add_const (f ω))
  have hG' := hbd G hGm
  have hM' := hbd (M T) hMt
  have hlim : Tendsto (fun n => |(∫ ω in A, h (ξ n ω + M T ω) ∂P) -
      ∫ ω in A, h (ξ n ω + G ω) ∂P|) atTop
      (𝓝 |(∫ ω in A, h (X ω + M T ω) ∂P) - ∫ ω in A, h (X ω + G ω) ∂P|) :=
    (hM'.sub hG').abs
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  exact shift_bound_simple P ℱ T hT M Sg hM sb hsb (ξ n) (S n) (hS n) (hξ n)
    G hGm hG hGind h hh hA

end A27Aux

/-- Lemma A.27 `M:B:newprob:conditional-heat` (source lines 10788-10817), bound
`B:newprob:conditional-bound`.  `(ℱ_r)_{0≤r≤T}` a filtration, `M` a continuous `ℝ^p`-valued
(local) martingale with `M_0 = 0`, `[M^a,M^b]_t = ∫_0^t Σ^{ab}_r dr` with `Σ` predictable
symmetric nonnegative and `E ∫_0^T tr Σ_r dr < ∞` (`B:newprob:bracket`; the integrability makes
`M` a square-integrable martingale, line 10822, which is how `IsVectorMartingaleWithCovariation`
states it), `Σ̄` deterministic measurable symmetric nonnegative integrable, `X` an
`ℱ_0`-measurable random vector, `G` a centered Gaussian vector independent of `ℱ_T` with covariance
`∫_0^T Σ̄_r dr`.  Then for `h ∈ C_b^2(ℝ^p)`, almost surely
`|E[h(X+M_T) | ℱ_0] - E[h(X+G) | ℱ_0]| ≤ ½ sup_x ‖D²h(x)‖_op E[∫_0^T ‖Σ_r - Σ̄_r‖_{S_1} dr | ℱ_0]`.
(The source's "an enlargement can be used to define `G`" is the existence of such a `G` on
`Ω × ℝ^p`, cf. `exists_enlargement`; it is not part of the inequality.)

PLAN (source proof 10819-10886 uses the backward heat equation and Itô's formula; the project's
route for Lemma A.21 avoids Itô calculus): conditional Lindeberg replacement.  For a bounded
nonnegative `ℱ_0`-measurable weight `ξ` it suffices to prove
`|E[ξ (h(X+M_T) - f(X))]| ≤ ½ ‖D²h‖ E[ξ ∫‖Σ-Σ̄‖]` with `f(x) := E h(x + G) = gaussSmooth h (∫Σ̄) x`
(`B:newprob:heat-definition` at `r = 0`), since `E[h(X+G) | ℱ_0] = f(X)` by independence of `G`
from `ℱ_T ⊇ ℱ_0` and `ℱ_0`-measurability of `X` (`condExp_indep_eq`-type lemma / Fubini).  Under
the tilted probability `P_ξ = ξ dP / E ξ`, `M` is still an `IsVectorMartingaleWithCovariation`
(tilting by an `ℱ_0`-measurable density preserves martingales, `condExp_mul_of_stronglyMeasurable_left`),
and `h̃(ω, y) := h(X ω + y)` is `C_b^2` in `y` with the same Hessian bound; run
`lindeberg_partition_bound`/`DM.lindeberg_discrete` (`HRS/Prob/MartingaleLindeberg.lean`) with
this `ℱ_0`-measurable random shift (the Taylor expansion of `gaussSmooth h̃` along the uniform
partition `unifPart T n` only uses `ℱ_{t_k}`-measurability of the shift, which holds for `ℱ_0`),
then `martingale_lindeberg_tendsto`, `gaussian_lindeberg_tendsto`, and the mollification step of
`multivariate_martingale_clt` (`gaussSmooth_approx`, `gaussSmooth_hessian`), finally remove the
regularisation of `Σ̄` as in A.21.  Conclude the a.s. inequality from the weighted inequality for
all bounded `ℱ_0`-measurable `ξ ≥ 0` (`ae_le_of_forall_setIntegral_le`-type lemma). -/
theorem conditional_gaussian_interpolation (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (X : Ω → (ℝ^p)) (hX : Measurable[ℱ 0] X)
    (G : Ω → (ℝ^p)) (hGm : AEMeasurable G P)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb))
    (hGind : Indep (MeasurableSpace.comap G inferInstance) (ℱ T) P)
    (h : (ℝ^p) → ℝ) (hh : MemCb 2 h) :
    ∀ᵐ ω ∂P,
      |(P[fun ω => h (X ω + M T ω) | ℱ 0]) ω - (P[fun ω => h (X ω + G ω) | ℱ 0]) ω| ≤
        (1 / 2) * hessSup h *
          (P[fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) | ℱ 0]) ω := by
  have hm : ℱ 0 ≤ mΩ := ℱ.le 0
  have hXm : Measurable X := hX.mono hm le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) with hg
  have hint1 : Integrable (fun ω => h (X ω + M T ω)) P :=
    integrable_memCb_comp P hh (hXm.aemeasurable.add hMt)
  have hint2 : Integrable (fun ω => h (X ω + G ω)) P :=
    integrable_memCb_comp P hh (hXm.aemeasurable.add hGm)
  have hintg : Integrable g P := LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  set U := P[fun ω => h (X ω + M T ω) | ℱ 0] with hU
  set V := P[fun ω => h (X ω + G ω) | ℱ 0] with hV
  set W := P[g | ℱ 0] with hW
  set c : ℝ := (1 / 2) * hessSup h with hc
  have hUm : StronglyMeasurable[ℱ 0] U := stronglyMeasurable_condExp
  have hVm : StronglyMeasurable[ℱ 0] V := stronglyMeasurable_condExp
  have hWm : StronglyMeasurable[ℱ 0] W := stronglyMeasurable_condExp
  have hUi : Integrable U P := integrable_condExp
  have hVi : Integrable V P := integrable_condExp
  have hWi : Integrable W P := integrable_condExp
  have hsetU : ∀ A, MeasurableSet[ℱ 0] A → ∫ ω in A, U ω ∂P = ∫ ω in A, h (X ω + M T ω) ∂P :=
    fun A hA => setIntegral_condExp hm hint1 hA
  have hsetV : ∀ A, MeasurableSet[ℱ 0] A → ∫ ω in A, V ω ∂P = ∫ ω in A, h (X ω + G ω) ∂P :=
    fun A hA => setIntegral_condExp hm hint2 hA
  have hsetW : ∀ A, MeasurableSet[ℱ 0] A → ∫ ω in A, W ω ∂P = ∫ ω in A, g ω ∂P :=
    fun A hA => setIntegral_condExp hm hintg hA
  have hSA : ∀ A, MeasurableSet[ℱ 0] A →
      |(∫ ω in A, U ω ∂P) - ∫ ω in A, V ω ∂P| ≤ c * ∫ ω in A, W ω ∂P := by
    intro A hA
    rw [hsetU A hA, hsetV A hA, hsetW A hA]
    exact shift_bound P ℱ T hT M Sg hM sb hsb X hX G hGm hG hGind h hh hA
  have h1 : (fun ω => U ω - V ω) ≤ᵐ[P] fun ω => c * W ω := by
    refine ae_le_of_setIntegral_le_trim P hm (hUm.sub hVm) (hWm.const_mul _) (hUi.sub hVi)
      (hWi.const_mul _) ?_
    intro A hA
    rw [integral_sub hUi.integrableOn hVi.integrableOn, integral_const_mul]
    have := hSA A hA
    rw [abs_le] at this
    linarith [this.2]
  have h2 : (fun ω => V ω - U ω) ≤ᵐ[P] fun ω => c * W ω := by
    refine ae_le_of_setIntegral_le_trim P hm (hVm.sub hUm) (hWm.const_mul _) (hVi.sub hUi)
      (hWi.const_mul _) ?_
    intro A hA
    rw [integral_sub hVi.integrableOn hUi.integrableOn, integral_const_mul]
    have := hSA A hA
    rw [abs_le] at this
    linarith [this.1]
  filter_upwards [h1, h2] with ω a b
  rw [abs_le]
  constructor <;> linarith

section A28Aux

omit [IsProbabilityMeasure P] in
lemma D3TestClass.memCb2 {h : (ℝ^p) → ℝ} (hh : h ∈ D3TestClass p) : MemCb 2 h :=
  ⟨hh.1.1.of_le (by norm_num), fun j hj => hh.1.2 j (hj.trans (by norm_num))⟩

omit [IsProbabilityMeasure P] in
lemma D3TestClass.hessSup_le {h : (ℝ^p) → ℝ} (hh : h ∈ D3TestClass p) : hessSup h ≤ 1 :=
  ciSup_le fun x => hh.2 2 (by norm_num) (by norm_num) x

omit [IsProbabilityMeasure P] in
lemma D3TestClass.lipschitz {h : (ℝ^p) → ℝ} (hh : h ∈ D3TestClass p) (x y : ℝ^p) :
    |h y - h x| ≤ ‖y - x‖ := by
  have hd : Differentiable ℝ h := hh.1.1.differentiable (by norm_num)
  have h1 : ∀ z, ‖fderiv ℝ h z‖ ≤ 1 := fun z => by
    rw [← norm_iteratedFDeriv_one]; exact hh.2 1 le_rfl (by norm_num) z
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := h) (s := Set.univ)
    (fun z _ => hd z) (fun z _ => h1 z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
  simpa using this

end A28Aux

/-- Corollary A.28 `M:B:newprob:conditional-martingale` (source lines 10888-10900), bound
`B:newprob:retained-initial-bound`: under the assumptions of Lemma A.27 and for an integrable
random vector `R`,
`𝖽₃(X + M_T + R, X + G) ≤ E|R| + ½ E ∫_0^T ‖Σ_r - Σ̄_r‖_{S_1} dr`, where `G` is independent of `X`
(it is independent of `ℱ_T ∋ X`).  No moment assumption on `X` is needed.

PLAN (lines 10902-10906): for `h ∈ D3TestClass p`, `|E h(X+M_T+R) - E h(X+M_T)| ≤ E|R|` by the
gradient bound (`norm_sub_le_of_mem_one`-type mean value inequality with `‖Dh‖ ≤ 1`); then take
expectations in `conditional_gaussian_interpolation` (`integral_condExp`, `hessSup h ≤ 1`) and the
supremum over the test class (`iSup_le`). -/
theorem retained_initial_law (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (X : Ω → (ℝ^p)) (hX : Measurable[ℱ 0] X)
    (G : Ω → (ℝ^p)) (hGm : AEMeasurable G P)
    (hG : law P G = multivariateGaussian 0 (integratedCov T sb))
    (hGind : Indep (MeasurableSpace.comap G inferInstance) (ℱ T) P)
    (R : Ω → (ℝ^p)) (hR : Integrable R P) :
    d3DistE (law P fun ω => X ω + M T ω + R ω) (law P fun ω => X ω + G ω) ≤
      ENNReal.ofReal (∫ ω, ‖R ω‖ ∂P + (1 / 2) * covDiscrepancyMatrix P T Sg sb) := by
  have hm : ℱ 0 ≤ mΩ := ℱ.le 0
  have hXm : Measurable X := hX.mono hm le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable R P := hR.aestronglyMeasurable.aemeasurable
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) with hg
  have hintg : Integrable g P := LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  have hg0 : 0 ≤ ∫ ω, g ω ∂P :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  have hRn : 0 ≤ ∫ ω, ‖R ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
  refine iSup_le fun ⟨h, hh⟩ => ?_
  have hh2 := D3TestClass.memCb2 hh
  rw [show covDiscrepancyMatrix P T Sg sb = ∫ ω, g ω ∂P from rfl]
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : ∫ x, h x ∂(law P fun ω => X ω + M T ω + R ω) = ∫ ω, h (X ω + M T ω + R ω) ∂P :=
    integral_map ((hXm.aemeasurable.add hMt).add hRm) hh.1.1.continuous.aestronglyMeasurable
  have e2 : ∫ x, h x ∂(law P fun ω => X ω + G ω) = ∫ ω, h (X ω + G ω) ∂P :=
    integral_map (hXm.aemeasurable.add hGm) hh.1.1.continuous.aestronglyMeasurable
  show |∫ x, h x ∂(law P fun ω => X ω + M T ω + R ω) - ∫ x, h x ∂(law P fun ω => X ω + G ω)| ≤ _
  rw [e1, e2]
  have hi1 : Integrable (fun ω => h (X ω + M T ω + R ω)) P :=
    integrable_memCb_comp P hh2 ((hXm.aemeasurable.add hMt).add hRm)
  have hi0 : Integrable (fun ω => h (X ω + M T ω)) P :=
    integrable_memCb_comp P hh2 (hXm.aemeasurable.add hMt)
  have hi2 : Integrable (fun ω => h (X ω + G ω)) P :=
    integrable_memCb_comp P hh2 (hXm.aemeasurable.add hGm)
  -- step 1: removing R
  have s1 : |(∫ ω, h (X ω + M T ω + R ω) ∂P) - ∫ ω, h (X ω + M T ω) ∂P| ≤ ∫ ω, ‖R ω‖ ∂P := by
    rw [← integral_sub hi1 hi0, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hR.norm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    simpa using D3TestClass.lipschitz hh (X ω + M T ω) (X ω + M T ω + R ω)
  -- step 2: Lemma A.27 integrated
  have hcond := conditional_gaussian_interpolation P ℱ T hT M Sg hM sb hsb X hX G hGm hG hGind h
    hh2
  have hUi : Integrable (P[fun ω => h (X ω + M T ω) | ℱ 0]) P := integrable_condExp
  have hVi : Integrable (P[fun ω => h (X ω + G ω) | ℱ 0]) P := integrable_condExp
  have hWi : Integrable (P[g | ℱ 0]) P := integrable_condExp
  have s2 : |(∫ ω, h (X ω + M T ω) ∂P) - ∫ ω, h (X ω + G ω) ∂P| ≤ (1 / 2) * ∫ ω, g ω ∂P := by
    rw [← integral_condExp hm (f := fun ω => h (X ω + M T ω)),
      ← integral_condExp hm (f := fun ω => h (X ω + G ω)), ← integral_sub hUi hVi,
      ← Real.norm_eq_abs]
    have hb : ∀ᵐ ω ∂P, ‖(P[fun ω => h (X ω + M T ω) | ℱ 0]) ω -
        (P[fun ω => h (X ω + G ω) | ℱ 0]) ω‖ ≤ (1 / 2) * hessSup h * (P[g | ℱ 0]) ω := by
      filter_upwards [hcond] with ω hω
      simpa [Real.norm_eq_abs] using hω
    refine (norm_integral_le_of_norm_le (hWi.const_mul ((1 / 2) * hessSup h)) hb).trans ?_
    rw [integral_const_mul, integral_condExp hm]
    have := D3TestClass.hessSup_le hh
    nlinarith
  have : (∫ ω, h (X ω + M T ω + R ω) ∂P) - ∫ ω, h (X ω + G ω) ∂P =
      ((∫ ω, h (X ω + M T ω + R ω) ∂P) - ∫ ω, h (X ω + M T ω) ∂P) +
        ((∫ ω, h (X ω + M T ω) ∂P) - ∫ ω, h (X ω + G ω) ∂P) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- The covariance `Q = ∑_i E[ζ_i ζ_iᵀ] + ∫_0^T Σ̄_r dr` of `B:newprob:total-covariance`. -/
def totalCovariance {N : ℕ} (ζ : Fin N → Ω → (ℝ^p)) (T : ℝ)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (Matrix.of fun a b => ∑ i, ∫ ω, ζ i ω a * ζ i ω b ∂P) + integratedCov T sb

/-! ### Route for Lemma A.29 (as formalised)

1. `R` is removed at cost `E|R|` (`D3TestClass.lipschitz`).
2. With `f := gaussSmooth h (∫Σ̄)` and `X = ∑ ζ_i`, the bound `|E h(X + M_T) - E f(X)| ≤ ½ E ∫‖Σ-Σ̄‖`
   is the G-free form of Lemma A.27 (`shift_bound_f`: Lemma A.21 under `P[· | B]`, `B ∈ ℱ_0`, for
   `ℱ_0`-simple approximations of `X`); no enlargement is needed.
3. Lindeberg replacement of the `ζ_i` by Gaussians `N(0, E ζ_iζ_iᵀ)` on the product of the laws
   (`lindeberg_pi_sharp`, a copy of `HRS.Yurinskii.lindeberg_pi` with the sharp third-order Taylor
   constant `1/6`, `taylor_sharp`), `f` having a `1`-Lipschitz Hessian (`gaussSmooth_hessian`).
4. The Gaussian third moment is at most `√3` times that of `ζ_i` (`gauss_m3_le_sqrt3`: Cauchy-Schwarz,
   `E|g|⁴ ≤ 3 (E|g|²)²`, Lyapunov).
5. `∑ g_i + G ∼ N(0, Q)` (`pi_map_sum_gauss`, `gaussSmooth_add`). -/

section A29Aux

/-- Third-order Taylor bound with the sharp constant `1/6`, for `f ∈ C²` with `L`-Lipschitz Hessian
(integral form of the remainder). -/
lemma taylor_sharp {f : (ℝ^p) → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ}
    (hL : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ L * ‖x - y‖) (x v : ℝ^p) :
    |f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v]| ≤
      L * ‖v‖ ^ 3 / 6 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  set q : ℝ → ℝ := fun s => fderiv ℝ (fderiv ℝ f) (x + s • v) v v with hq
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := by
    intro s; simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + s • v) v) s :=
    fun s => (hd1 (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hφ' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v) (q s) s := by
    intro s
    have h1 := (hd2 (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt s h1
  set Ψ : ℝ → ℝ := fun s => f (x + s • v) + (1 - s) * fderiv ℝ f (x + s • v) v with hΨdef
  have hΨ : ∀ s : ℝ, HasDerivAt Ψ ((1 - s) * q s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have := (hφ s).add (h1.mul (hφ' s))
    convert this using 1
    ring
  have hqc : Continuous q := by
    have : Continuous fun s : ℝ => fderiv ℝ (fderiv ℝ f) (x + s • v) :=
      hc2.comp (continuous_const.add (continuous_id.smul continuous_const))
    exact (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
      ((ContinuousLinearMap.apply ℝ ((ℝ^p) →L[ℝ] ℝ) v).continuous.comp this)
  have hFTC : ∫ s in (0 : ℝ)..1, (1 - s) * q s = Ψ 1 - Ψ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hΨ s)
      ((by fun_prop : Continuous fun s : ℝ => (1 - s) * q s).intervalIntegrable _ _)
  have hB : iteratedFDeriv ℝ 2 f x ![v, v] = q 0 := by
    simp [hq, iteratedFDeriv_two_apply]
  have h12 : ∫ s in (0 : ℝ)..1, (1 - s) = 1 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp; norm_num
  have hR : f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v] =
      ∫ s in (0 : ℝ)..1, (1 - s) * (q s - q 0) := by
    have e1 : ∫ s in (0 : ℝ)..1, (1 - s) * (q s - q 0) =
        (∫ s in (0 : ℝ)..1, (1 - s) * q s) - q 0 * ∫ s in (0 : ℝ)..1, (1 - s) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
      · refine intervalIntegral.integral_congr fun s _ => ?_
        show (1 - s) * (q s - q 0) = (1 - s) * q s - q 0 * (1 - s)
        ring
      · exact (by fun_prop : Continuous fun s : ℝ => (1 - s) * q s).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s : ℝ => q 0 * (1 - s)).intervalIntegrable _ _
    rw [e1, hFTC, h12, hB]
    simp [hΨdef]
    ring
  rw [hR]
  have hqb : ∀ s ∈ Set.Icc (0 : ℝ) 1, |q s - q 0| ≤ L * s * ‖v‖ ^ 3 := by
    intro s hs
    have : q s - q 0 = (iteratedFDeriv ℝ 2 f (x + s • v) - iteratedFDeriv ℝ 2 f x) ![v, v] := by
      simp [hq, iteratedFDeriv_two_apply]
    rw [this, ← Real.norm_eq_abs]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have h5 := hL (x + s • v) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1] at h5
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    calc ‖iteratedFDeriv ℝ 2 f (x + s • v) - iteratedFDeriv ℝ 2 f x‖ * (‖v‖ * ‖v‖)
        ≤ (L * (s * ‖v‖)) * (‖v‖ * ‖v‖) := by gcongr
      _ = L * s * ‖v‖ ^ 3 := by ring
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (g := fun s => (1 - s) * (L * s * ‖v‖ ^ 3)) (Filter.Eventually.of_forall fun s hs => ?_)
    ((by fun_prop : Continuous fun s : ℝ => (1 - s) * (L * s * ‖v‖ ^ 3)).intervalIntegrable _ _)).trans ?_
  · rw [norm_mul, Real.norm_eq_abs (1 - s), Real.norm_eq_abs, abs_of_nonneg (by linarith [hs.2])]
    exact mul_le_mul_of_nonneg_left (hqb s ⟨hs.1.le, hs.2⟩) (by linarith [hs.2])
  · have : (fun s : ℝ => (1 - s) * (L * s * ‖v‖ ^ 3)) =
        fun s => (L * ‖v‖ ^ 3) * s - (L * ‖v‖ ^ 3) * s ^ 2 := by ext s; ring
    rw [this, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    · norm_num; linarith
    · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _


structure SharpFn (K : ℝ) (f : (ℝ^p) → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  K_nonneg : 0 ≤ K
  bdd0 : ∃ M, ∀ x, |f x| ≤ M
  bdd1 : ∃ M, ∀ x, ‖fderiv ℝ f x‖ ≤ M
  bdd2 : ∃ M, ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M
  taylor : ∀ x v : ℝ^p, |f (x + v) - f x - fderiv ℝ f x v -
    (1 / 2) * fderiv ℝ (fderiv ℝ f) x v v| ≤ K * ‖v‖ ^ 3

lemma SharpFn.measurable {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f) : Measurable f :=
  hf.contDiff.continuous.measurable

lemma SharpFn.continuous_fderiv {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f) :
    Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)

lemma SharpFn.continuous_fderiv2 {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f) :
    Continuous (fderiv ℝ (fderiv ℝ f)) :=
  (hf.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero

section SharpLind

variable {P}

/-- Core estimate of one Lindeberg step. -/
lemma swap_step_sharp {X Y : Ω → (ℝ^p)} {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f)
    (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (hY0 : ∀ c, ∫ ω, Y ω c ∂P = 0)
    (hY3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) :
    |∫ ω, f (X ω + Y ω) ∂P - ∫ ω, f (X ω) ∂P -
      (1 / 2) * ∑ c, ∑ d, (∫ ω, fderiv ℝ (fderiv ℝ f) (X ω) (EuclideanSpace.single c 1)
        (EuclideanSpace.single d 1) ∂P) * ∫ ω, Y ω c * Y ω d ∂P| ≤
      K * ∫ ω, ‖Y ω‖ ^ 3 ∂P := by
  obtain ⟨M0, hM0⟩ := hf.bdd0
  obtain ⟨M1, hM1⟩ := hf.bdd1
  obtain ⟨M2, hM2⟩ := hf.bdd2
  obtain ⟨hY1, hY2⟩ := Yurinskii.integrable_norm_of_pow3 hY hY3
  set g : Fin p → (ℝ^p) → ℝ := fun c x => fderiv ℝ f x (EuclideanSpace.single c 1) with hg
  set H : Fin p → Fin p → (ℝ^p) → ℝ := fun c d x =>
    fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single c 1) (EuclideanSpace.single d 1) with hH
  have hgc : ∀ c, Continuous (g c) := fun c => by
    simp only [hg]
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single c 1)).continuous.comp
      hf.continuous_fderiv
  have hHc : ∀ c d, Continuous (H c d) := fun c d => by
    simp only [hH]
    exact ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single d 1)).continuous.comp
      ((ContinuousLinearMap.apply ℝ ((ℝ^p) →L[ℝ] ℝ) (EuclideanSpace.single c 1)).continuous.comp
      hf.continuous_fderiv2))
  have hgb : ∀ c x, |g c x| ≤ M1 := fun c x => by
    have := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single c 1)
    rw [Yurinskii.norm_single_one, mul_one, Real.norm_eq_abs] at this
    exact this.trans (hM1 x)
  have hHb : ∀ c d x, |H c d x| ≤ M2 := fun c d x => by
    have h1 := (fderiv ℝ (fderiv ℝ f) x).le_opNorm (EuclideanSpace.single c 1)
    have h2 := (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single c 1)).le_opNorm
      (EuclideanSpace.single d 1)
    rw [Yurinskii.norm_single_one, mul_one] at h1 h2
    rw [Real.norm_eq_abs] at h2
    exact (h2.trans (h1.trans (hM2 x)))
  have hYc : ∀ c, Measurable fun ω => Y ω c := fun c => by fun_prop
  have hYcI : ∀ c, Integrable (fun ω => Y ω c) P := fun c =>
    hY1.mono' (hYc c).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact Yurinskii.norm_coord_le _ _)
  have hYcdI : ∀ c d, Integrable (fun ω => Y ω c * Y ω d) P := fun c d =>
    hY2.mono' ((hYc c).mul (hYc d)).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |Y ω c| * |Y ω d| ≤ ‖Y ω‖ * ‖Y ω‖ :=
            mul_le_mul (Yurinskii.norm_coord_le _ _) (Yurinskii.norm_coord_le _ _) (abs_nonneg _) (norm_nonneg _)
        _ = ‖Y ω‖ ^ 2 := by ring)
  have hfI : ∀ Z : Ω → (ℝ^p), Measurable Z → Integrable (fun ω => f (Z ω)) P := fun Z hZ =>
    (integrable_const M0).mono' (hf.measurable.comp hZ).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM0 _)
  have hXY : Measurable fun ω => X ω + Y ω := hX.add hY
  have hlinI : ∀ c, Integrable (fun ω => Y ω c * g c (X ω)) P := fun c =>
    (hY1.mul_const M1).mono' ((hYc c).mul ((hgc c).measurable.comp hX)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (Yurinskii.norm_coord_le _ _) (hgb _ _) (abs_nonneg _) (norm_nonneg _))
  have hquadI : ∀ c d, Integrable (fun ω => Y ω c * Y ω d * H c d (X ω)) P := fun c d =>
    (hY2.mul_const M2).mono' (((hYc c).mul (hYc d)).mul ((hHc c d).measurable.comp hX)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc |Y ω c| * |Y ω d| * |H c d (X ω)| ≤ ‖Y ω‖ * ‖Y ω‖ * M2 :=
              mul_le_mul (mul_le_mul (Yurinskii.norm_coord_le _ _) (Yurinskii.norm_coord_le _ _) (abs_nonneg _)
                (norm_nonneg _)) (hHb _ _ _) (abs_nonneg _) (by positivity)
          _ = ‖Y ω‖ ^ 2 * M2 := by ring)
  -- independence
  have hlin : ∀ c, ∫ ω, Y ω c * g c (X ω) ∂P = 0 := by
    intro c
    have hi : IndepFun (fun ω => g c (X ω)) (fun ω => Y ω c) P :=
      hind.comp (φ := g c) (ψ := fun y : (ℝ^p) => y c) (hgc c).measurable (by fun_prop)
    have := hi.integral_fun_mul_eq_mul_integral
      ((hgc c).measurable.comp hX).aestronglyMeasurable (hYc c).aestronglyMeasurable
    calc ∫ ω, Y ω c * g c (X ω) ∂P = ∫ ω, g c (X ω) * Y ω c ∂P := by
          congr 1; ext ω; ring
      _ = 0 := by rw [this, hY0 c, mul_zero]
  have hquad : ∀ c d, ∫ ω, Y ω c * Y ω d * H c d (X ω) ∂P =
      (∫ ω, H c d (X ω) ∂P) * ∫ ω, Y ω c * Y ω d ∂P := by
    intro c d
    have hi : IndepFun (fun ω => H c d (X ω)) (fun ω => Y ω c * Y ω d) P :=
      hind.comp (φ := H c d) (ψ := fun y : (ℝ^p) => y c * y d) (hHc c d).measurable (by fun_prop)
    have := hi.integral_fun_mul_eq_mul_integral
      ((hHc c d).measurable.comp hX).aestronglyMeasurable ((hYc c).mul (hYc d)).aestronglyMeasurable
    calc ∫ ω, Y ω c * Y ω d * H c d (X ω) ∂P = ∫ ω, H c d (X ω) * (Y ω c * Y ω d) ∂P := by
          congr 1; ext ω; ring
      _ = _ := this
  -- remainder
  set R : Ω → ℝ := fun ω => f (X ω + Y ω) - f (X ω) - ∑ c, Y ω c * g c (X ω) -
    (1 / 2) * ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω) with hR
  have hRb : ∀ ω, |R ω| ≤ K * ‖Y ω‖ ^ 3 := by
    intro ω
    have h := hf.taylor (X ω) (Y ω)
    have e1 : fderiv ℝ f (X ω) (Y ω) = ∑ c, Y ω c * g c (X ω) := Yurinskii.expand1 _ _
    have e2 : fderiv ℝ (fderiv ℝ f) (X ω) (Y ω) (Y ω) =
        ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω) := Yurinskii.expand2 _ _
    rw [e1, e2] at h
    simpa only [hR, sub_sub] using h
  have hlinSum : Integrable (fun ω => ∑ c, Y ω c * g c (X ω)) P :=
    integrable_finsetSum _ fun c _ => hlinI c
  have hquadSum : Integrable (fun ω => ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω)) P :=
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hquadI c d
  have hI12 : Integrable (fun ω => f (X ω + Y ω) - f (X ω)) P := (hfI _ hXY).sub (hfI X hX)
  have hI123 : Integrable (fun ω => f (X ω + Y ω) - f (X ω) - ∑ c, Y ω c * g c (X ω)) P :=
    hI12.sub hlinSum
  have hI4 : Integrable (fun ω => (1 / 2 : ℝ) * ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω)) P :=
    hquadSum.const_mul _
  have hRI : Integrable R P := hI123.sub hI4
  have hRint : ∫ ω, R ω ∂P = ∫ ω, f (X ω + Y ω) ∂P - ∫ ω, f (X ω) ∂P -
      (1 / 2) * ∑ c, ∑ d, (∫ ω, H c d (X ω) ∂P) * ∫ ω, Y ω c * Y ω d ∂P := by
    simp only [hR]
    rw [integral_sub hI123 hI4, integral_sub hI12 hlinSum, integral_sub (hfI _ hXY) (hfI X hX),
      integral_const_mul, integral_finsetSum _ fun c _ => hlinI c,
      integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hquadI c d]
    simp_rw [integral_finsetSum _ fun d _ => hquadI _ d, hlin, hquad]
    simp
  have : |∫ ω, R ω ∂P| ≤ K * ∫ ω, ‖Y ω‖ ^ 3 ∂P := by
    calc |∫ ω, R ω ∂P| ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, K * ‖Y ω‖ ^ 3 ∂P := integral_mono hRI.abs (hY3.const_mul K) hRb
      _ = _ := integral_const_mul _ _
  rw [hRint] at this
  exact this

/-- One Lindeberg swap. -/
lemma swap_diff_sharp {X Y Z : Ω → (ℝ^p)} {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hindY : IndepFun X Y P) (hindZ : IndepFun X Z P)
    (hY0 : ∀ c, ∫ ω, Y ω c ∂P = 0) (hZ0 : ∀ c, ∫ ω, Z ω c ∂P = 0)
    (hYZ : ∀ c d, ∫ ω, Y ω c * Y ω d ∂P = ∫ ω, Z ω c * Z ω d ∂P)
    (hY3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) (hZ3 : Integrable (fun ω => ‖Z ω‖ ^ 3) P) :
    |∫ ω, f (X ω + Y ω) ∂P - ∫ ω, f (X ω + Z ω) ∂P| ≤
      K * (∫ ω, ‖Y ω‖ ^ 3 ∂P + ∫ ω, ‖Z ω‖ ^ 3 ∂P) := by
  have h1 := swap_step_sharp hf hX hY hindY hY0 hY3
  have h2 := swap_step_sharp hf hX hZ hindZ hZ0 hZ3
  simp_rw [hYZ] at h1
  set a := ∫ ω, f (X ω + Y ω) ∂P
  set b := ∫ ω, f (X ω + Z ω) ∂P
  set q := (1 / 2 : ℝ) * ∑ c, ∑ d, (∫ ω, fderiv ℝ (fderiv ℝ f) (X ω) (EuclideanSpace.single c 1)
        (EuclideanSpace.single d 1) ∂P) * ∫ ω, Z ω c * Z ω d ∂P
  have : |a - b| ≤ |a - ∫ ω, f (X ω) ∂P - q| + |b - ∫ ω, f (X ω) ∂P - q| := by
    have := abs_sub (a - ∫ ω, f (X ω) ∂P - q) (b - ∫ ω, f (X ω) ∂P - q)
    calc |a - b| = |(a - ∫ ω, f (X ω) ∂P - q) - (b - ∫ ω, f (X ω) ∂P - q)| := by ring_nf
      _ ≤ _ := this
  calc |a - b| ≤ _ := this
    _ ≤ K * ∫ ω, ‖Y ω‖ ^ 3 ∂P + K * ∫ ω, ‖Z ω‖ ^ 3 ∂P := add_le_add h1 h2
    _ = _ := by ring


/-- Lindeberg telescoping over the hybrid sums. -/
theorem lindeberg_telescope_sharp {N : ℕ} {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f)
    (V : Fin N ⊕ Fin N → Ω → (ℝ^p)) (hVm : ∀ t, Measurable (V t)) (hV : iIndepFun V P)
    (h0 : ∀ t c, ∫ ω, V t ω c ∂P = 0)
    (h2 : ∀ i c d, ∫ ω, V (Sum.inl i) ω c * V (Sum.inl i) ω d ∂P =
      ∫ ω, V (Sum.inr i) ω c * V (Sum.inr i) ω d ∂P)
    (h3 : ∀ t, Integrable (fun ω => ‖V t ω‖ ^ 3) P) :
    |∫ ω, f (∑ i, V (Sum.inl i) ω) ∂P - ∫ ω, f (∑ i, V (Sum.inr i) ω) ∂P| ≤
      K * ∑ i, (∫ ω, ‖V (Sum.inl i) ω‖ ^ 3 ∂P + ∫ ω, ‖V (Sum.inr i) ω‖ ^ 3 ∂P) := by
  classical
  -- hybrid sums
  let W : ℕ → Ω → (ℝ^p) := fun k ω => ∑ i : Fin N,
    (if i.val < k then V (Sum.inl i) ω else V (Sum.inr i) ω)
  let a : ℕ → ℝ := fun k => ∫ ω, f (W k ω) ∂P
  have hW0 : ∀ ω, W 0 ω = ∑ i, V (Sum.inr i) ω := fun ω => by simp [W]
  have hWN : ∀ ω, W N ω = ∑ i, V (Sum.inl i) ω := fun ω => by
    simp only [W]
    exact Finset.sum_congr rfl fun i _ => by simp [i.2]
  -- one step
  have hstep : ∀ k : ℕ, ∀ hk : k < N, |a (k + 1) - a k| ≤
      K * (∫ ω, ‖V (Sum.inl ⟨k, hk⟩) ω‖ ^ 3 ∂P + ∫ ω, ‖V (Sum.inr ⟨k, hk⟩) ω‖ ^ 3 ∂P) := by
    intro k hk
    set j : Fin N := ⟨k, hk⟩ with hj
    let s : Fin N → Fin N ⊕ Fin N := fun i => if i.val < k then Sum.inl i else Sum.inr i
    have hs_inj : Function.Injective s := by
      intro i i' h
      simp only [s] at h
      split_ifs at h with h1 h2 h2 <;> simp_all
    set X : Ω → (ℝ^p) := fun ω => ∑ i ∈ Finset.univ.erase j, V (s i) ω with hX
    have hXm : Measurable X := by
      simp only [hX]
      exact Finset.measurable_sum _ fun i _ => hVm _
    have hXeq : X = ∑ t ∈ (Finset.univ.erase j).image s, V t := by
      rw [Finset.sum_image (fun i _ i' _ h => hs_inj h)]
      ext ω; simp [hX]
    have hnotl : Sum.inl j ∉ (Finset.univ.erase j).image s := by
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, not_exists, not_and]
      intro i hij h
      apply hij
      simp only [s] at h
      split_ifs at h with h1 <;> simp_all
    have hnotr : Sum.inr j ∉ (Finset.univ.erase j).image s := by
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, not_exists, not_and]
      intro i hij h
      apply hij
      simp only [s] at h
      split_ifs at h with h1 <;> simp_all
    have hindl : IndepFun X (V (Sum.inl j)) P := by
      rw [hXeq]; exact hV.indepFun_finsetSum_of_notMem hVm hnotl
    have hindr : IndepFun X (V (Sum.inr j)) P := by
      rw [hXeq]; exact hV.indepFun_finsetSum_of_notMem hVm hnotr
    have hWk1 : ∀ ω, W (k + 1) ω = X ω + V (Sum.inl j) ω := by
      intro ω
      simp only [W, hX]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_comm]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have : i.val ≠ k := fun h => hij (Fin.ext h)
        simp only [s]
        by_cases hlt : i.val < k
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have : ¬ i.val < k + 1 := by omega
          simp [hlt, this]
      · simp [hj]
    have hWk : ∀ ω, W k ω = X ω + V (Sum.inr j) ω := by
      intro ω
      simp only [W, hX]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_comm]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp only [s]
        split_ifs <;> rfl
      · simp [hj]
    have := swap_diff_sharp hf hXm (hVm _) (hVm _) hindl hindr (h0 _) (h0 _) (h2 j) (h3 _) (h3 _)
    simp only [a, hWk1, hWk]
    exact this
  have hsum : a N - a 0 = ∑ k ∈ Finset.range N, (a (k + 1) - a k) := (Finset.sum_range_sub a N).symm
  have haN : a N = ∫ ω, f (∑ i, V (Sum.inl i) ω) ∂P := by simp only [a, hWN]
  have ha0 : a 0 = ∫ ω, f (∑ i, V (Sum.inr i) ω) ∂P := by simp only [a, hW0]
  rw [← haN, ← ha0, hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  let B : ℕ → ℝ := fun k => if hk : k < N then
    K * (∫ ω, ‖V (Sum.inl ⟨k, hk⟩) ω‖ ^ 3 ∂P + ∫ ω, ‖V (Sum.inr ⟨k, hk⟩) ω‖ ^ 3 ∂P) else 0
  calc ∑ k ∈ Finset.range N, |a (k + 1) - a k| ≤ ∑ k ∈ Finset.range N, B k :=
        Finset.sum_le_sum fun k hk => by
          have hk' : k < N := Finset.mem_range.1 hk
          simp only [B, dif_pos hk']
          exact hstep k hk'
    _ = ∑ i : Fin N, B i := (Fin.sum_univ_eq_sum_range B N).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [B, dif_pos i.2]

lemma integral_comp_eval_a29 {ι : Type*} [Fintype ι] (μ : ι → Measure (ℝ^p)) [∀ i, IsProbabilityMeasure (μ i)]
    (t : ι) (g : (ℝ^p) → ℝ) (hg : Measurable g) :
    ∫ ω, g (ω t) ∂(Measure.pi μ) = ∫ x, g x ∂(μ t) := by
  have hmp := measurePreserving_eval μ t
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable]

lemma integrable_comp_eval_a29 {ι : Type*} [Fintype ι] (μ : ι → Measure (ℝ^p)) [∀ i, IsProbabilityMeasure (μ i)]
    (t : ι) (g : (ℝ^p) → ℝ) (hg : Measurable g) (h : Integrable g (μ t)) :
    Integrable (fun ω => g (ω t)) (Measure.pi μ) := by
  have hmp := measurePreserving_eval μ t
  rw [← hmp.map_eq] at h
  exact (integrable_map_measure hg.aestronglyMeasurable hmp.measurable.aemeasurable).1 h

/-- Lindeberg replacement on product measures. -/
theorem lindeberg_pi_sharp {N : ℕ} {K : ℝ} {f : (ℝ^p) → ℝ} (hf : SharpFn K f)
    (ρ γ : Fin N → Measure (ℝ^p)) [∀ i, IsProbabilityMeasure (ρ i)] [∀ i, IsProbabilityMeasure (γ i)]
    (h0ρ : ∀ i c, ∫ x, x c ∂(ρ i) = 0) (h0γ : ∀ i c, ∫ x, x c ∂(γ i) = 0)
    (h2 : ∀ i c d, ∫ x, x c * x d ∂(ρ i) = ∫ x, x c * x d ∂(γ i))
    (h3ρ : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ρ i))
    (h3γ : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (γ i)) :
    |∫ x, f x ∂((Measure.pi ρ).map (fun p => ∑ i, p i)) -
        ∫ x, f x ∂((Measure.pi γ).map (fun p => ∑ i, p i))| ≤
      K * ∑ i, (∫ x, ‖x‖ ^ 3 ∂(ρ i) + ∫ x, ‖x‖ ^ 3 ∂(γ i)) := by
  classical
  set μ : Fin N ⊕ Fin N → Measure (ℝ^p) := Sum.elim ρ γ with hμ
  haveI : ∀ t, IsProbabilityMeasure (μ t) := fun t => by
    rcases t with i | i <;> simp [hμ] <;> infer_instance
  set Q : Measure (Fin N ⊕ Fin N → (ℝ^p)) := Measure.pi μ with hQ
  let V : Fin N ⊕ Fin N → (Fin N ⊕ Fin N → (ℝ^p)) → (ℝ^p) := fun t ω => ω t
  have hVm : ∀ t, Measurable (V t) := fun t => measurable_pi_apply t
  have hV : iIndepFun V Q := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hcoord : ∀ c : Fin p, Measurable fun x : (ℝ^p) => x c := fun c => by fun_prop
  -- moments
  have e0 : ∀ t c, ∫ ω, V t ω c ∂Q = ∫ x, x c ∂(μ t) := fun t c =>
    integral_comp_eval_a29 μ t (fun x => x c) (hcoord c)
  have e2 : ∀ t c d, ∫ ω, V t ω c * V t ω d ∂Q = ∫ x, x c * x d ∂(μ t) := fun t c d =>
    integral_comp_eval_a29 μ t (fun x => x c * x d) ((hcoord c).mul (hcoord d))
  have e3 : ∀ t, ∫ ω, ‖V t ω‖ ^ 3 ∂Q = ∫ x, ‖x‖ ^ 3 ∂(μ t) := fun t =>
    integral_comp_eval_a29 μ t (fun x => ‖x‖ ^ 3) (measurable_norm.pow_const 3)
  have i3 : ∀ t, Integrable (fun ω => ‖V t ω‖ ^ 3) Q := by
    intro t
    refine integrable_comp_eval_a29 μ t (fun x => ‖x‖ ^ 3) (measurable_norm.pow_const 3) ?_
    rcases t with i | i
    · exact h3ρ i
    · exact h3γ i
  have key := lindeberg_telescope_sharp hf V hVm hV
    (fun t c => by rw [e0]; rcases t with i | i; exacts [h0ρ i c, h0γ i c])
    (fun i c d => by rw [e2, e2]; exact h2 i c d) i3
  -- identify the laws
  have hlaw : ∀ (g : Fin N → Measure (ℝ^p)) [∀ i, IsProbabilityMeasure (g i)] (inj : Fin N → Fin N ⊕ Fin N),
      Function.Injective inj → (∀ i, μ (inj i) = g i) →
      Q.map (fun ω i => ω (inj i)) = Measure.pi g := by
    intro g _ inj hinj hg
    have h1 := hV.precomp hinj
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hVm _).aemeasurable)] at h1
    have hmap_i : ∀ i, Q.map (V (inj i)) = g i := by
      intro i
      have := (measurePreserving_eval μ (inj i)).map_eq
      rw [← hg i, ← this]
    simp_rw [hmap_i] at h1
    exact h1
  have hsum : ∀ (g : Fin N → Measure (ℝ^p)) [∀ i, IsProbabilityMeasure (g i)] (inj : Fin N → Fin N ⊕ Fin N),
      Function.Injective inj → (∀ i, μ (inj i) = g i) →
      ∫ ω, f (∑ i, V (inj i) ω) ∂Q = ∫ x, f x ∂((Measure.pi g).map (fun p => ∑ i, p i)) := by
    intro g _ inj hinj hg
    have hsm : Measurable (fun p : Fin N → (ℝ^p) => ∑ i, p i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hmq : Measurable (fun (ω : Fin N ⊕ Fin N → (ℝ^p)) (i : Fin N) => ω (inj i)) :=
      Measurable.of_eval fun i => measurable_pi_apply _
    rw [integral_map hsm.aemeasurable hf.measurable.aestronglyMeasurable, ← hlaw g inj hinj hg]
    exact (integral_map hmq.aemeasurable ((hf.measurable.comp hsm).aestronglyMeasurable :
        AEStronglyMeasurable (fun x : Fin N → (ℝ^p) => f (∑ i, x i)) _)).symm
  rw [← hsum ρ Sum.inl Sum.inl_injective (fun i => rfl),
    ← hsum γ Sum.inr Sum.inr_injective (fun i => rfl)]
  refine key.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e3, e3]; rfl

end SharpLind

omit [IsProbabilityMeasure P] in
lemma D3TestClass.hess_lip {h : (ℝ^p) → ℝ} (hh : h ∈ D3TestClass p) (x y : ℝ^p) :
    ‖iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y‖ ≤ 1 * ‖x - y‖ := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ 2 h) :=
    hh.1.1.differentiable_iteratedFDeriv (by norm_cast)
  have h1 : ∀ z, ‖fderiv ℝ (iteratedFDeriv ℝ 2 h) z‖ ≤ 1 := fun z => by
    rw [norm_fderiv_iteratedFDeriv]; exact hh.2 3 (by norm_num) le_rfl z
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := iteratedFDeriv ℝ 2 h)
    (s := Set.univ) (fun z _ => hd z) (fun z _ => h1 z) convex_univ (Set.mem_univ y)
    (Set.mem_univ x)
  simpa using this

omit [IsProbabilityMeasure P] in
lemma D3TestClass.sharpFn {h : (ℝ^p) → ℝ} (hh : h ∈ D3TestClass p)
    {Q : Matrix (Fin p) (Fin p) ℝ} (hQ : Q.PosSemidef) : SharpFn (1 / 6) (gaussSmooth h Q) := by
  have hh2 : ContDiff ℝ 2 h := hh.1.1.of_le (by norm_num)
  have hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ 1 := fun x => hh.2 2 (by norm_num) (by norm_num) x
  obtain ⟨hu2, huH, huL⟩ := gaussSmooth_hessian Q hQ h hh2 1 hH
  obtain ⟨hd1, -, -⟩ := LindebergAux.gaussSmooth_derivs Q h hh2 1 hH
  have hLu := huL 1 (D3TestClass.hess_lip hh)
  obtain ⟨C, hC⟩ := memCb_bound (D3TestClass.memCb2 hh)
  refine ⟨hu2, by norm_num, ⟨C, fun x => ?_⟩, ⟨1, fun x => ?_⟩, ⟨1, fun x => ?_⟩, fun x v => ?_⟩
  · have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : ℝ^p) Q) (C := C)
      (f := fun z => h (x + z)) (ae_of_all _ fun z => by simpa using hC (x + z))
    simpa [gaussSmooth] using this
  · rw [(hd1 x).fderiv]
    have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : ℝ^p) Q) (C := 1)
      (f := fun z => fderiv ℝ h (x + z)) (ae_of_all _ fun z => by
        rw [← norm_iteratedFDeriv_one]; exact hh.2 1 le_rfl (by norm_num) _)
    simpa using this
  · rw [← LindebergAux.norm_iter2]; exact huH x
  · have := taylor_sharp hu2 hLu x v
    simp only [iteratedFDeriv_two_apply] at this
    refine this.trans (le_of_eq ?_)
    ring

lemma gauss_m3_le_sqrt3 (ρ : Measure (ℝ^p)) [IsProbabilityMeasure ρ]
    (h3 : Integrable (fun x : ℝ^p => ‖x‖ ^ 3) ρ) :
    ∫ y, ‖y‖ ^ 3 ∂(multivariateGaussian (0 : ℝ^p) (Yurinskii.momentMatrix ρ)) ≤
      Real.sqrt 3 * ∫ x, ‖x‖ ^ 3 ∂ρ := by
  have h2 : Integrable (fun x : ℝ^p => ‖x‖ ^ 2) ρ :=
    (Yurinskii.integrable_norm_of_pow3 (P := ρ) (Y := id) measurable_id h3).2
  have hQ := Yurinskii.momentMatrix_posSemidef ρ h2
  set γ := multivariateGaussian (0 : ℝ^p) (Yurinskii.momentMatrix ρ) with hγ
  set m2 := ∫ x, ‖x‖ ^ 2 ∂ρ with hm2
  set m3 := ∫ x, ‖x‖ ^ 3 ∂ρ with hm3
  have hm20 : 0 ≤ m2 := integral_nonneg fun x => by positivity
  have hm30 : 0 ≤ m3 := integral_nonneg fun x => by positivity
  have hm2γ : ∫ y, ‖y‖ ^ 2 ∂γ = m2 := by
    rw [hγ, Yurinskii.integral_norm_sq_gauss hQ, Yurinskii.trace_momentMatrix ρ h2]
  have hb : ∫ y, ‖y‖ ^ 4 ∂γ ≤ 3 * m2 ^ 2 := by
    have := Yurinskii.integral_norm_pow4_le hQ
    rw [Yurinskii.trace_momentMatrix ρ h2] at this
    have e : Yurinskii.c4 = 3 := gauss_m4
    rwa [e] at this
  have i1 : Integrable (fun y : ℝ^p => ‖y‖ ^ 1) γ := Yurinskii.integrable_norm_pow_gauss 1 (by norm_num)
  have i2 : Integrable (fun y : ℝ^p => ‖y‖ ^ 2) γ := Yurinskii.integrable_norm_pow_gauss 2 (by norm_num)
  have i3 : Integrable (fun y : ℝ^p => ‖y‖ ^ 3) γ := Yurinskii.integrable_norm_pow_gauss 3 (by norm_num)
  have i4 : Integrable (fun y : ℝ^p => ‖y‖ ^ 4) γ := Yurinskii.integrable_norm_pow_gauss 4 (by norm_num)
  set a := ∫ y, ‖y‖ ^ 3 ∂γ with ha
  set b := ∫ y, ‖y‖ ^ 4 ∂γ with hbdef
  have ha0 : 0 ≤ a := integral_nonneg fun y => by positivity
  -- Cauchy-Schwarz
  have hcs : a ^ 2 ≤ m2 * b := by
    refine Yurinskii.sq_le_mul_of_quad (fun t => ?_)
    have h0 : 0 ≤ ∫ y, (t * ‖y‖ ^ 1 - ‖y‖ ^ 2) ^ 2 ∂γ := integral_nonneg fun y => sq_nonneg _
    have e : ∀ y : ℝ^p, (t * ‖y‖ ^ 1 - ‖y‖ ^ 2) ^ 2 =
        (t * t) * ‖y‖ ^ 2 + (-2 * t) * ‖y‖ ^ 3 + ‖y‖ ^ 4 := fun y => by ring
    simp_rw [e] at h0
    have j1 : Integrable (fun y : ℝ^p => (t * t) * ‖y‖ ^ 2) γ := i2.const_mul _
    have j2 : Integrable (fun y : ℝ^p => (-2 * t) * ‖y‖ ^ 3) γ := i3.const_mul _
    have j12 : Integrable (fun y : ℝ^p => (t * t) * ‖y‖ ^ 2 + (-2 * t) * ‖y‖ ^ 3) γ := j1.add j2
    rw [integral_add j12 i4, integral_add j1 j2, integral_const_mul,
      integral_const_mul, hm2γ] at h0
    linarith
  have hlya := Yurinskii.lyapunov ρ h2 h3
  have hm2c : m2 ^ 3 ≤ m3 ^ 2 := by
    have h1 : (Real.sqrt m2) ^ 6 ≤ m3 ^ 2 := by
      have := pow_le_pow_left₀ (pow_nonneg (Real.sqrt_nonneg _) 3) hlya 2
      simpa [← pow_mul] using this
    have h2' : (Real.sqrt m2) ^ 6 = m2 ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hm20]
    linarith
  have hsq : a ^ 2 ≤ (Real.sqrt 3 * m3) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    calc a ^ 2 ≤ m2 * b := hcs
      _ ≤ m2 * (3 * m2 ^ 2) := mul_le_mul_of_nonneg_left hb hm20
      _ = 3 * m2 ^ 3 := by ring
      _ ≤ 3 * m3 ^ 2 := by linarith
  by_contra hlt
  push Not at hlt
  have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
  linarith

lemma shift_bound_f_simple (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (ξ : Ω → (ℝ^p)) (S : Finset (ℝ^p)) (hS : ∀ ω, ξ ω ∈ S)
    (hξ : ∀ x, MeasurableSet[ℱ 0] (ξ ⁻¹' {x}))
    (h : (ℝ^p) → ℝ) (hh : MemCb 2 h) (f : (ℝ^p) → ℝ) (hfc : Continuous f)
    (hf : ∀ x, f x = ∫ z, h (x + z) ∂(multivariateGaussian 0 (integratedCov T sb)))
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    |(∫ ω in A, h (ξ ω + M T ω) ∂P) - ∫ ω in A, f (ξ ω) ∂P| ≤
      (1 / 2) * hessSup h * ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  obtain ⟨C, hC⟩ := memCb_bound hh
  have hfb : ∀ x, |f x| ≤ C := fun x => by
    rw [hf x]
    have := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : ℝ^p) (integratedCov T sb)) (C := C)
      (f := fun z => h (x + z)) (ae_of_all _ fun z => by simpa using hC (x + z))
    simpa using this
  have hm0 : ∀ B, MeasurableSet[ℱ 0] B → MeasurableSet B := fun B hB => ℱ.le 0 _ hB
  have hξm : ∀ x, MeasurableSet (ξ ⁻¹' {x}) := fun x => hm0 _ (hξ x)
  have hξmeas : Measurable ξ := by
    intro s _
    have : ξ ⁻¹' s = ⋃ x ∈ (S.filter (· ∈ s)), ξ ⁻¹' {x} := by
      ext ω; simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop,
        Finset.mem_filter]
      exact ⟨fun h => ⟨ξ ω, ⟨hS ω, h⟩, rfl⟩, fun ⟨x, ⟨_, hx⟩, e⟩ => e ▸ hx⟩
    rw [this]
    exact Finset.measurableSet_biUnion _ fun x _ => hξm x
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hint1 : Integrable (fun ω => h (ξ ω + M T ω)) P :=
    integrable_memCb_comp P hh (hξmeas.aemeasurable.add hMt)
  have hint2 : Integrable (fun ω => f (ξ ω)) P :=
    Integrable.of_bound (C := C) (hfc.measurable.comp hξmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa using hfb (ξ ω))
  have hintg : Integrable (fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) P :=
    LindebergAux.Iblk_integrable P ℱ hM hsb.meas hsb.int le_rfl le_rfl
  rw [setIntegral_fiber_sum P (hm0 A hA) S ξ hS hξm hint1,
    setIntegral_fiber_sum P (hm0 A hA) S ξ hS hξm hint2,
    setIntegral_fiber_sum P (hm0 A hA) S ξ hS hξm hintg, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  have hB : MeasurableSet[ℱ 0] (A ∩ ξ ⁻¹' {x}) := hA.inter (hξ x)
  have hBm := hm0 _ hB
  have e1 : ∫ ω in A ∩ ξ ⁻¹' {x}, h (ξ ω + M T ω) ∂P = ∫ ω in A ∩ ξ ⁻¹' {x}, h (x + M T ω) ∂P :=
    setIntegral_congr_fun hBm fun ω hω => by rw [show ξ ω = x from hω.2]
  have e2 : ∫ ω in A ∩ ξ ⁻¹' {x}, f (ξ ω) ∂P = P.real (A ∩ ξ ⁻¹' {x}) * f x := by
    rw [setIntegral_congr_fun hBm (g := fun _ => f x) fun ω hω => by rw [show ξ ω = x from hω.2],
      setIntegral_const, smul_eq_mul]
  rw [e1, e2, hf x]
  exact const_shift_bound P ℱ T hT M Sg hM sb hsb h hh x hB

lemma shift_bound_f (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    (X : Ω → (ℝ^p)) (hX : Measurable[ℱ 0] X)
    (h : (ℝ^p) → ℝ) (hh : MemCb 2 h) (f : (ℝ^p) → ℝ) (hfc : Continuous f)
    (hf : ∀ x, f x = ∫ z, h (x + z) ∂(multivariateGaussian 0 (integratedCov T sb)))
    {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    |(∫ ω in A, h (X ω + M T ω) ∂P) - ∫ ω in A, f (X ω) ∂P| ≤
      (1 / 2) * hessSup h * ∫ ω in A, (∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  obtain ⟨ξ, S, hS, hξ, hξm0, hξt⟩ := exists_finrange_approx_a27 (m := ℱ 0) hX
  have hAm : MeasurableSet A := ℱ.le 0 _ hA
  have hξm : ∀ n, Measurable (ξ n) := fun n => (hξm0 n).mono (ℱ.le 0) le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  obtain ⟨C, hC⟩ := memCb_bound hh
  have hfb : ∀ x, |f x| ≤ C := fun x => by
    rw [hf x]
    have := norm_integral_le_of_norm_le_const
      (μ := multivariateGaussian (0 : ℝ^p) (integratedCov T sb)) (C := C)
      (f := fun z => h (x + z)) (ae_of_all _ fun z => by simpa using hC (x + z))
    simpa using this
  have hbd1 : Tendsto (fun n => ∫ ω in A, h (ξ n ω + M T ω) ∂P) atTop
      (𝓝 (∫ ω in A, h (X ω + M T ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
      (integrable_const C) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (integrable_memCb_comp (P.restrict A) hh
        ((hξm n).aemeasurable.add hMt.restrict)).aestronglyMeasurable
    · simpa using hC _
    · exact (hh.1.continuous.tendsto _).comp ((hξt ω).add_const (M T ω))
  have hbd2 : Tendsto (fun n => ∫ ω in A, f (ξ n ω) ∂P) atTop (𝓝 (∫ ω in A, f (X ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_)
      (integrable_const C) (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
    · exact (hfc.measurable.comp (hξm n)).aestronglyMeasurable
    · simpa using hfb _
    · exact (hfc.tendsto _).comp (hξt ω)
  have hlim := (hbd1.sub hbd2).abs
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  exact shift_bound_f_simple P ℱ T hT M Sg hM sb hsb (ξ n) (S n) (hS n) (hξ n) h hh f hfc hf hA

lemma integratedCov_psd {T : ℝ} {sb : ℝ → Matrix (Fin p) (Fin p) ℝ} (hsb : IsDetCovMatrix T sb) :
    (integratedCov T sb).PosSemidef :=
  LindebergAux.covBlock_psd hsb.psd (LindebergAux.sb_entry_integrableOn hsb.meas hsb.int hsb.psd)
    le_rfl le_rfl

/-- The Lindeberg part of Lemma A.29: for independent centred `ζ_i` with finite third moments
and `f = gaussSmooth h Γ`, `|E f(∑ ζ_i) - ∫ h dN(0, ∑ E ζ_iζ_iᵀ + Γ)| ≤ (1+√3)/6 ∑ E|ζ_i|³`. -/
lemma initial_lindeberg {N : ℕ} (ζ : Fin N → Ω → (ℝ^p)) (hζm : ∀ i, Measurable (ζ i))
    (hζind : iIndepFun ζ P) (hζcent : ∀ i, ∫ ω, ζ i ω ∂P = 0)
    (hζ3 : ∀ i, Integrable (fun ω => ‖ζ i ω‖ ^ 3) P)
    {Γ : Matrix (Fin p) (Fin p) ℝ} (hΓ : Γ.PosSemidef) {h : (ℝ^p) → ℝ} (hh : h ∈ D3TestClass p) :
    |(∫ ω, gaussSmooth h Γ (∑ i, ζ i ω) ∂P) -
        ∫ y, h y ∂(multivariateGaussian (0 : ℝ^p)
          ((Matrix.of fun a b => ∑ i, ∫ ω, ζ i ω a * ζ i ω b ∂P) + Γ))| ≤
      (1 + Real.sqrt 3) / 6 * ∑ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P := by
  classical
  set ρ : Fin N → Measure (ℝ^p) := fun i => P.map (ζ i) with hρ
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (hζm i).aemeasurable).2 inferInstance
  have hρ3 : ∀ i, Integrable (fun x : ℝ^p => ‖x‖ ^ 3) (ρ i) := fun i =>
    (integrable_map_measure (measurable_norm.pow_const 3).aestronglyMeasurable
      (hζm i).aemeasurable).2 (hζ3 i)
  have hρ2 : ∀ i, Integrable (fun x : ℝ^p => ‖x‖ ^ 2) (ρ i) := fun i =>
    (Yurinskii.integrable_norm_of_pow3 (P := ρ i) (Y := id) measurable_id (hρ3 i)).2
  have hρ1 : ∀ i, Integrable (fun x : ℝ^p => ‖x‖) (ρ i) := fun i =>
    (Yurinskii.integrable_norm_of_pow3 (P := ρ i) (Y := id) measurable_id (hρ3 i)).1
  have hQ : ∀ i, (Yurinskii.momentMatrix (ρ i)).PosSemidef := fun i =>
    Yurinskii.momentMatrix_posSemidef _ (hρ2 i)
  set γ : Fin N → Measure (ℝ^p) := fun i =>
    multivariateGaussian (0 : ℝ^p) (Yurinskii.momentMatrix (ρ i)) with hγ
  -- the moments of ρ
  have hζi : ∀ i, Integrable (ζ i) P := fun i => by
    refine Integrable.mono' (hζ3 i |>.add (integrable_const 1)) (hζm i).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply]
    rcases le_total ‖ζ i ω‖ 1 with h1 | h1
    · nlinarith [pow_nonneg (norm_nonneg (ζ i ω)) 3]
    · nlinarith [norm_nonneg (ζ i ω), mul_nonneg (norm_nonneg (ζ i ω)) (sq_nonneg (‖ζ i ω‖ - 1))]
  have h0ρ : ∀ i c, ∫ x, x c ∂(ρ i) = 0 := by
    intro i c
    have e1 : ∫ x, x c ∂(ρ i) = ∫ ω, ζ i ω c ∂P :=
      integral_map (hζm i).aemeasurable (by fun_prop)
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj c : (ℝ^p) →L[ℝ] ℝ)
      (hζi i)
    rw [e1]
    simpa [hζcent i] using this
  have h2ρ : ∀ i c d, ∫ x, x c * x d ∂(ρ i) = ∫ x, x c * x d ∂(γ i) := by
    intro i c d
    simp only [hγ]
    rw [Yurinskii.integral_coord_mul (hQ i)]
    rfl
  have key := lindeberg_pi_sharp (D3TestClass.sharpFn hh hΓ) ρ γ h0ρ
    (fun i c => Yurinskii.integral_coord_zero c) h2ρ hρ3
    (fun i => Yurinskii.integrable_norm_pow_gauss 3 (by norm_num))
  have hsm : Measurable (fun x : Fin N → ℝ^p => ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hvec : Measurable (fun ω i => ζ i ω) := Measurable.of_eval hζm
  have hind := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hζm i).aemeasurable)).1 hζind
  have hf := D3TestClass.sharpFn hh hΓ
  have hSmap : P.map (fun ω => ∑ i, ζ i ω) = (Measure.pi ρ).map (fun x => ∑ i, x i) := by
    rw [← show (Measure.pi fun i => P.map (ζ i)) = Measure.pi ρ from rfl, ← hind,
      Measure.map_map hsm hvec]
    rfl
  have hSm : Measurable (fun ω => ∑ i, ζ i ω) := Finset.measurable_sum _ fun i _ => hζm i
  have e1 : ∫ ω, gaussSmooth h Γ (∑ i, ζ i ω) ∂P =
      ∫ x, gaussSmooth h Γ x ∂((Measure.pi ρ).map (fun x => ∑ i, x i)) := by
    rw [← hSmap, integral_map hSm.aemeasurable hf.contDiff.continuous.aestronglyMeasurable]
  have e2 : (Measure.pi γ).map (fun x => ∑ i, x i) =
      multivariateGaussian (0 : ℝ^p) (∑ i, Yurinskii.momentMatrix (ρ i)) :=
    Yurinskii.pi_map_sum_gauss _ hQ
  rw [e2] at key
  have hA : (Matrix.of fun a b => ∑ i, ∫ ω, ζ i ω a * ζ i ω b ∂P) =
      ∑ i, Yurinskii.momentMatrix (ρ i) := by
    ext a b
    simp only [Matrix.of_apply, Matrix.sum_apply, Yurinskii.momentMatrix, hρ]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (integral_map (hζm i).aemeasurable
      ((by fun_prop : Measurable fun x : ℝ^p => x a * x b).aestronglyMeasurable)).symm
  have hAsum : (∑ i, Yurinskii.momentMatrix (ρ i)).PosSemidef :=
    Matrix.posSemidef_sum _ fun i _ => hQ i
  have e3 : ∫ x, gaussSmooth h Γ x ∂(multivariateGaussian (0 : ℝ^p)
      (∑ i, Yurinskii.momentMatrix (ρ i))) =
      ∫ y, h y ∂(multivariateGaussian (0 : ℝ^p) ((∑ i, Yurinskii.momentMatrix (ρ i)) + Γ)) := by
    have := gaussSmooth_add (∑ i, Yurinskii.momentMatrix (ρ i)) Γ hAsum hΓ h
      (hh.1.1.of_le (by norm_num)) 1 (fun x => hh.2 2 (by norm_num) (by norm_num) x) 0
    simp only [gaussSmooth, zero_add] at this
    exact this.symm
  have e4 : ∀ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i) = ∫ ω, ‖ζ i ω‖ ^ 3 ∂P := fun i =>
    integral_map (hζm i).aemeasurable (measurable_norm.pow_const 3).aestronglyMeasurable
  rw [e1, hA, ← e3]
  refine key.trans ?_
  have hm3 : ∀ i, ∫ x, ‖x‖ ^ 3 ∂(γ i) ≤ Real.sqrt 3 * ∫ x, ‖x‖ ^ 3 ∂(ρ i) := fun i =>
    gauss_m3_le_sqrt3 (ρ i) (hρ3 i)
  have : ∑ i, (∫ x, ‖x‖ ^ 3 ∂(ρ i) + ∫ x, ‖x‖ ^ 3 ∂(γ i)) ≤
      (1 + Real.sqrt 3) * ∑ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hm3 i
    rw [e4] at this ⊢
    nlinarith
  calc 1 / 6 * ∑ i, (∫ x, ‖x‖ ^ 3 ∂(ρ i) + ∫ x, ‖x‖ ^ 3 ∂(γ i))
      ≤ 1 / 6 * ((1 + Real.sqrt 3) * ∑ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
    _ = _ := by ring

end A29Aux

/-- Lemma A.29 `M:B:newprob:initial-martingale` (source lines 10908-10931), bound
`B:newprob:main-bound`: in the setting of Lemma A.27 (`M`, `Σ`, `Σ̄`, `ℱ`), let `ζ_1,…,ζ_N` be
independent, centered, `ℱ_0`-measurable random vectors in `ℝ^p` with finite third absolute
moments, `R` an integrable random vector, and `G_Q` the centered Gaussian with covariance
`Q = ∑_i E[ζ_i ζ_iᵀ] + ∫_0^T Σ̄_r dr`.  Then
`𝖽₃(∑_i ζ_i + M_T + R, G_Q) ≤ E|R| + (1+√3)/6 ∑_i E|ζ_i|³ + ½ E ∫_0^T ‖Σ_r - Σ̄_r‖_{S_1} dr`.
The constants are absolute (independent of `T` and of the smallest eigenvalues of `Q`).
No Gaussian `G` of Lemma A.27 appears in the statement: it is built in the proof.

PLAN (lines 10933-10976): remove `R` at cost `E|R|`; build `G` independent of `ℱ_T` with
covariance `∫Σ̄` on the enlargement `Ω × ℝ^p` (`Measure.prod` with `multivariateGaussian`; the
hypotheses of `conditional_gaussian_interpolation` transfer to the product filtration
`ℱ_r ⊗ ⊥`, and `d3DistE` of the pulled-back laws is unchanged) and apply
`conditional_gaussian_interpolation` with `X = ∑ ζ_i`, integrating.  Then
`f(x) := E h(x + G) = gaussSmooth h (∫Σ̄) x ∈ C_b^3` with derivative norms `≤` those of `h`
(`gaussSmooth_derivs`), and the Lindeberg replacement `B:newprob:lindeberg-bound` of the `ζ_i` by
independent Gaussians `g_i ∼ N(0, E ζ_iζ_iᵀ)` on a further product space, one summand at a time,
with the third-order Taylor remainder `taylor_bound_of_mem`/`taylor_two_remainder` (cost
`(E|ζ_i|³ + E|g_i|³)/6`) and the Gaussian third-moment bound
`E|g_i|³ ≤ √3 (E|ζ_i|²)^{3/2} ≤ √3 E|ζ_i|³` (`B:newprob:gaussian-third-moment`: Gaussian fourth
moment identity `E|g|⁴ = (tr Q)² + 2 tr(Q²)`, `integral_norm_sq_mvGaussian`, Cauchy–Schwarz and
Jensen/`Real.rpow` monotonicity of `L^p` norms).  Finally `∑ g_i + G ∼ N(0,Q)` (`mvGaussian_conv`). -/
theorem initial_sum_martingale (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    {N : ℕ} (ζ : Fin N → Ω → (ℝ^p)) (hζmeas : ∀ i, Measurable[ℱ 0] (ζ i))
    (hζind : iIndepFun ζ P) (hζcent : ∀ i, ∫ ω, ζ i ω ∂P = 0)
    (hζ3 : ∀ i, Integrable (fun ω => ‖ζ i ω‖ ^ 3) P)
    (R : Ω → (ℝ^p)) (hR : Integrable R P) :
    d3DistE (law P fun ω => ∑ i, ζ i ω + M T ω + R ω)
        (multivariateGaussian 0 (totalCovariance P ζ T sb)) ≤
      ENNReal.ofReal (∫ ω, ‖R ω‖ ∂P + (1 + Real.sqrt 3) / 6 * ∑ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P +
        (1 / 2) * covDiscrepancyMatrix P T Sg sb) := by
  classical
  have hm : ℱ 0 ≤ mΩ := ℱ.le 0
  have hζm' : ∀ i, Measurable (ζ i) := fun i => (hζmeas i).mono hm le_rfl
  have hS0 : Measurable[ℱ 0] (fun ω => ∑ i, ζ i ω) :=
    Finset.measurable_sum (m := ℱ 0) _ fun i _ => hζmeas i
  have hSm : Measurable (fun ω => ∑ i, ζ i ω) := hS0.mono hm le_rfl
  have hMt : AEMeasurable (M T) P :=
    (hM.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRm : AEMeasurable R P := hR.aestronglyMeasurable.aemeasurable
  have hΓ := integratedCov_psd hsb
  set g : Ω → ℝ := fun ω => ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) with hg
  have hg0 : 0 ≤ ∫ ω, g ω ∂P :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  have hRn : 0 ≤ ∫ ω, ‖R ω‖ ∂P := integral_nonneg fun ω => norm_nonneg _
  have hζ3n : 0 ≤ ∑ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P :=
    Finset.sum_nonneg fun i _ => integral_nonneg fun ω => by positivity
  refine iSup_le fun ⟨h, hh⟩ => ?_
  have hh2 := D3TestClass.memCb2 hh
  refine ENNReal.ofReal_le_ofReal ?_
  have e1 : ∫ x, h x ∂(law P fun ω => ∑ i, ζ i ω + M T ω + R ω) =
      ∫ ω, h (∑ i, ζ i ω + M T ω + R ω) ∂P :=
    integral_map ((hSm.aemeasurable.add hMt).add hRm) hh.1.1.continuous.aestronglyMeasurable
  show |∫ x, h x ∂(law P fun ω => ∑ i, ζ i ω + M T ω + R ω) -
      ∫ x, h x ∂(multivariateGaussian (0 : ℝ^p) (totalCovariance P ζ T sb))| ≤ _
  rw [e1]
  have hi1 : Integrable (fun ω => h (∑ i, ζ i ω + M T ω + R ω)) P :=
    integrable_memCb_comp P hh2 ((hSm.aemeasurable.add hMt).add hRm)
  have hi0 : Integrable (fun ω => h (∑ i, ζ i ω + M T ω)) P :=
    integrable_memCb_comp P hh2 (hSm.aemeasurable.add hMt)
  -- (a) removing R
  have sa : |(∫ ω, h (∑ i, ζ i ω + M T ω + R ω) ∂P) - ∫ ω, h (∑ i, ζ i ω + M T ω) ∂P| ≤
      ∫ ω, ‖R ω‖ ∂P := by
    rw [← integral_sub hi1 hi0, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hR.norm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    simpa using D3TestClass.lipschitz hh (∑ i, ζ i ω + M T ω) (∑ i, ζ i ω + M T ω + R ω)
  -- (b) the interpolation with the shift `∑ ζ_i`
  have hf := D3TestClass.sharpFn hh hΓ
  have sb' := shift_bound_f P ℱ T hT M Sg hM sb hsb (fun ω => ∑ i, ζ i ω) hS0 h hh2
    (gaussSmooth h (integratedCov T sb)) hf.contDiff.continuous (fun x => rfl)
    (A := Set.univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at sb'
  have sb2 : |(∫ ω, h (∑ i, ζ i ω + M T ω) ∂P) -
      ∫ ω, gaussSmooth h (integratedCov T sb) (∑ i, ζ i ω) ∂P| ≤ (1 / 2) * ∫ ω, g ω ∂P := by
    refine sb'.trans ?_
    have := D3TestClass.hessSup_le hh
    nlinarith
  -- (c) Lindeberg replacement and Gaussian convolution
  have sc := initial_lindeberg P ζ hζm' hζind hζcent hζ3 hΓ hh
  have e2 : totalCovariance P ζ T sb =
      (Matrix.of fun a b => ∑ i, ∫ ω, ζ i ω a * ζ i ω b ∂P) + integratedCov T sb := rfl
  rw [e2]
  set X1 := ∫ ω, h (∑ i, ζ i ω + M T ω + R ω) ∂P
  set X2 := ∫ ω, h (∑ i, ζ i ω + M T ω) ∂P
  set X3 := ∫ ω, gaussSmooth h (integratedCov T sb) (∑ i, ζ i ω) ∂P
  set X4 := ∫ y, h y ∂(multivariateGaussian (0 : ℝ^p)
    ((Matrix.of fun a b => ∑ i, ∫ ω, ζ i ω a * ζ i ω b ∂P) + integratedCov T sb))
  have : X1 - X4 = (X1 - X2) + (X2 - X3) + (X3 - X4) := by ring
  rw [this]
  refine (abs_add_three _ _ _).trans ?_
  have hcov : covDiscrepancyMatrix P T Sg sb = ∫ ω, g ω ∂P := rfl
  rw [hcov]
  linarith

/-- Corollary A.30 `M:B:newprob:iid` (source lines 10978-10994): `x_1,…,x_N` independent with law
`μ` (on a measurable space `E`), `ℱ_0`-measurable, and `f ∈ L³(μ; ℝ^p)` deterministic; Lemma A.29
applies to `ζ_i = N^{-1/2}(f(x_i) - ∫ f dμ)` (`B:newprob:iid-vector`), with total covariance
`Q = Cov_μ(f) + ∫_0^T Σ̄_r dr`, and its initial-data term equals
`(1+√3)/(6√N) ∫ |f - ∫ f dμ|³ dμ` (`B:newprob:iid-third-moment`, first expression).  `f` and `μ`
may depend on `N` and on the observation times (they are arbitrary parameters here).

PLAN: the `ζ_i` are independent (`iIndepFun.comp`), centered, `ℱ_0`-measurable, with
`E|ζ_i|³ = N^{-3/2} ∫|f - ∫f|³ dμ` (change of variables `integral_map`), so
`initial_sum_martingale` applies and `∑_i E|ζ_i|³ = N^{-1/2} ∫|f - ∫f|³ dμ`; the covariance
`∑_i E ζ_iζ_iᵀ = Cov_μ(f)` likewise. -/
theorem iid_initial_sampling (ℱ : Filtration ℝ mΩ) (T : ℝ) (hT : 0 ≤ T)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ T M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsb : IsDetCovMatrix T sb)
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Ω → E) (hxmeas : ∀ i, Measurable[ℱ 0] (x i))
    (hxind : iIndepFun x P) (hxlaw : ∀ i, law P (x i) = μ)
    (f : E → (ℝ^p)) (hf : MemLp f 3 μ)
    (R : Ω → (ℝ^p)) (hR : Integrable R P) :
    let m : ℝ^p := ∫ y, f y ∂μ
    let Q : Matrix (Fin p) (Fin p) ℝ :=
      (Matrix.of fun a b => ∫ y, (f y a - m a) * (f y b - m b) ∂μ) + integratedCov T sb
    d3DistE (law P fun ω => ∑ i, (Real.sqrt N)⁻¹ • (f (x i ω) - m) + M T ω + R ω)
        (multivariateGaussian 0 Q) ≤
      ENNReal.ofReal (∫ ω, ‖R ω‖ ∂P +
        (1 + Real.sqrt 3) / (6 * Real.sqrt N) * ∫ y, ‖f y - m‖ ^ 3 ∂μ +
        (1 / 2) * covDiscrepancyMatrix P T Sg sb) := by
  intro m Q
  classical
  have hm0 : ℱ 0 ≤ mΩ := ℱ.le 0
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set sN : ℝ := Real.sqrt N with hsN
  have hsN0 : 0 < sN := Real.sqrt_pos.2 hN0
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt hN0.le
  -- a measurable representative of `f`
  set ft : E → (ℝ^p) := hf.aestronglyMeasurable.mk f with hft
  have hftm : StronglyMeasurable ft := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfae : f =ᵐ[μ] ft := hf.aestronglyMeasurable.ae_eq_mk
  have hmt : m = ∫ y, ft y ∂μ := integral_congr_ae hfae
  have hft3 : MemLp ft 3 μ := MemLp.ae_eq hfae hf
  set φ : E → (ℝ^p) := fun y => sN⁻¹ • (ft y - m) with hφ
  have hφm : Measurable φ := (hftm.measurable.sub_const m).const_smul sN⁻¹
  set ζ : Fin N → Ω → (ℝ^p) := fun i ω => φ (x i ω) with hζ
  have hxm : ∀ i, Measurable (x i) := fun i => (hxmeas i).mono hm0 le_rfl
  have hζmeas : ∀ i, Measurable[ℱ 0] (ζ i) := fun i => hφm.comp (hxmeas i)
  have hζind : iIndepFun ζ P := hxind.comp (fun _ => φ) (fun _ => hφm)
  -- moments of `φ` under `μ`
  have hI3 : Integrable (fun y => ‖ft y - m‖ ^ 3) μ :=
    (hft3.sub (memLp_const m)).integrable_norm_pow (by norm_num)
  have hφ3 : ∀ y, ‖φ y‖ ^ 3 = (sN⁻¹) ^ 3 * ‖ft y - m‖ ^ 3 := fun y => by
    simp only [hφ, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hsN0, mul_pow]
  have hφ3i : Integrable (fun y => ‖φ y‖ ^ 3) μ := by
    simp_rw [hφ3]; exact hI3.const_mul _
  have hmapx : ∀ i, P.map (x i) = μ := hxlaw
  have kvec : ∀ (i : Fin N) (g : E → ℝ^p), Measurable g →
      ∫ ω, g (x i ω) ∂P = ∫ y, g y ∂μ := fun i g hg => by
    rw [← hmapx i]; exact (integral_map (hxm i).aemeasurable hg.aestronglyMeasurable).symm
  have kreal : ∀ (i : Fin N) (g : E → ℝ), Measurable g →
      ∫ ω, g (x i ω) ∂P = ∫ y, g y ∂μ := fun i g hg => by
    rw [← hmapx i]; exact (integral_map (hxm i).aemeasurable hg.aestronglyMeasurable).symm
  have hζ3 : ∀ i, Integrable (fun ω => ‖ζ i ω‖ ^ 3) P := fun i => by
    have h1 : Integrable (fun y => ‖φ y‖ ^ 3) (P.map (x i)) := by rw [hmapx i]; exact hφ3i
    exact (integrable_map_measure (measurable_norm.pow_const 3 |>.comp hφm).aestronglyMeasurable
      (hxm i).aemeasurable).1 h1
  have hφi : Integrable φ μ := by
    refine Integrable.mono' (hφ3i.add (integrable_const 1)) hφm.aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply]
    rcases le_total ‖φ y‖ 1 with h1 | h1
    · nlinarith [pow_nonneg (norm_nonneg (φ y)) 3]
    · nlinarith [norm_nonneg (φ y), mul_nonneg (norm_nonneg (φ y)) (sq_nonneg (‖φ y‖ - 1))]
  have hint_ft : Integrable ft μ := hft3.integrable (by norm_num)
  have hφ0 : ∫ y, φ y ∂μ = 0 := by
    simp only [hφ]
    rw [integral_smul, integral_sub hint_ft (integrable_const m), ← hmt]
    simp
  have hζcent : ∀ i, ∫ ω, ζ i ω ∂P = 0 := fun i => by
    simp only [hζ]
    rw [kvec i φ hφm, hφ0]
  have hA := initial_sum_martingale P ℱ T hT M Sg hM sb hsb ζ hζmeas hζind hζcent hζ3 R hR
  -- identification of the quantities
  have hFae : (fun ω => ∑ i, sN⁻¹ • (f (x i ω) - m) + M T ω + R ω) =ᵐ[P]
      (fun ω => ∑ i, ζ i ω + M T ω + R ω) := by
    have : ∀ i, (fun ω => f (x i ω)) =ᵐ[P] (fun ω => ft (x i ω)) := fun i =>
      ae_eq_comp (hxm i).aemeasurable (by rw [hmapx i]; exact hfae)
    have hall := ae_all_iff.2 this
    filter_upwards [hall] with ω hω
    simp only [hζ, hφ]
    rw [Finset.sum_congr rfl fun i _ => by rw [hω i]]
  have hlaw : (law P fun ω => ∑ i, sN⁻¹ • (f (x i ω) - m) + M T ω + R ω) =
      law P fun ω => ∑ i, ζ i ω + M T ω + R ω := Measure.map_congr hFae
  have hQ : totalCovariance P ζ T sb = Q := by
    unfold totalCovariance
    congr 1
    ext a b
    simp only [Matrix.of_apply]
    have : ∀ i, ∫ ω, ζ i ω a * ζ i ω b ∂P = (sN⁻¹) ^ 2 * ∫ y, (f y a - m a) * (f y b - m b) ∂μ := by
      intro i
      have e1 : ∫ ω, ζ i ω a * ζ i ω b ∂P =
          ∫ y, φ y a * φ y b ∂μ :=
        kreal i (fun y => φ y a * φ y b)
          ((by fun_prop : Measurable fun y : ℝ^p => y a * y b).comp hφm)
      rw [e1]
      have e2 : ∫ y, φ y a * φ y b ∂μ = ∫ y, (sN⁻¹) ^ 2 * ((f y a - m a) * (f y b - m b)) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hfae] with y hy
        simp only [hφ, ← hy, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        ring
      rw [e2, integral_const_mul]
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_pow, hsN2]
    field_simp
  have hS3 : ∑ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P = (sN)⁻¹ * ∫ y, ‖f y - m‖ ^ 3 ∂μ := by
    have : ∀ i, ∫ ω, ‖ζ i ω‖ ^ 3 ∂P = (sN⁻¹) ^ 3 * ∫ y, ‖f y - m‖ ^ 3 ∂μ := by
      intro i
      have e1 : ∫ ω, ‖ζ i ω‖ ^ 3 ∂P = ∫ y, ‖φ y‖ ^ 3 ∂μ :=
        kreal i (fun y => ‖φ y‖ ^ 3) (measurable_norm.pow_const 3 |>.comp hφm)
      rw [e1]
      simp_rw [hφ3]
      rw [integral_const_mul]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hfae] with y hy
      rw [← hy]
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (N : ℝ) * (sN⁻¹) ^ 3 = sN⁻¹ := by
      rw [inv_pow, ← hsN2]; field_simp
    rw [← mul_assoc, this]
  rw [hlaw, ← hQ]
  refine hA.trans (le_of_eq ?_)
  congr 1
  rw [hS3]
  field_simp

lemma cube_tangent {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) : a ^ 3 + 3 * a ^ 2 * (t - a) ≤ t ^ 3 := by
  nlinarith [mul_nonneg (sq_nonneg (t - a)) (add_nonneg ht (mul_nonneg two_pos.le ha))]

lemma cube_add_le {x b : ℝ} (hx : 0 ≤ x) (hb : 0 ≤ b) : (x + b) ^ 3 ≤ 4 * (x ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (sq_nonneg (x - b)) (add_nonneg hx hb), mul_nonneg hx hb,
    sq_nonneg (x - b), mul_nonneg (mul_nonneg hx hb) (add_nonneg hx hb)]

/-- Corollary A.30, display `B:newprob:iid-third-moment`, second inequality (source lines
10987-10989, proof 10996-10999): `∫ |f - ∫ f dμ|³ dμ ≤ 8 ∫ |f|³ dμ` for `f ∈ L³(μ;ℝ^p)` (Minkowski
and Jensen: `‖f - ∫f‖_{L³} ≤ 2 ‖f‖_{L³}`), so that the initial-data term is at most
`4(1+√3)/(3√N) ∫|f|³ dμ`; "if `f` is centered the factor `8` is unnecessary" is the identity
`f - ∫ f dμ = f` in that case.

PLAN: `eLpNorm_sub_le` (Minkowski in `L³`), `‖∫ f dμ‖ ≤ ∫ ‖f‖ dμ ≤ (∫‖f‖³)^{1/3}` (Jensen /
`eLpNorm_le_eLpNorm_of_exponent_le` on a probability space), then cube. -/
theorem iid_third_moment_centering {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (f : E → (ℝ^p)) (hf : MemLp f 3 μ) :
    ∫ y, ‖f y - ∫ z, f z ∂μ‖ ^ 3 ∂μ ≤ 8 * ∫ y, ‖f y‖ ^ 3 ∂μ := by
  have hf1 : Integrable f μ := hf.integrable (by norm_num)
  have hn1 : Integrable (fun y => ‖f y‖) μ := hf1.norm
  have hn3 : Integrable (fun y => ‖f y‖ ^ 3) μ := hf.integrable_norm_pow (by norm_num)
  set a : ℝ := ∫ y, ‖f y‖ ∂μ with ha
  have ha0 : 0 ≤ a := integral_nonneg fun y => norm_nonneg _
  set m : ℝ^p := ∫ z, f z ∂μ with hm
  have hma : ‖m‖ ≤ a := norm_integral_le_integral_norm f
  -- Jensen for the cube
  have hJ : a ^ 3 ≤ ∫ y, ‖f y‖ ^ 3 ∂μ := by
    have hs : Integrable (fun y => ‖f y‖ - a) μ := hn1.sub (integrable_const a)
    have h1 : ∫ y, (a ^ 3 + 3 * a ^ 2 * (‖f y‖ - a)) ∂μ ≤ ∫ y, ‖f y‖ ^ 3 ∂μ :=
      integral_mono ((integrable_const _).add (hs.const_mul _)) hn3
        fun y => cube_tangent ha0 (norm_nonneg _)
    have h2 : ∫ y, (a ^ 3 + 3 * a ^ 2 * (‖f y‖ - a)) ∂μ = a ^ 3 := by
      rw [integral_add (integrable_const _) (hs.const_mul _),
        integral_const_mul, integral_sub hn1 (integrable_const _)]
      simp [ha]
    linarith
  have hmb : ‖m‖ ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hma 3
  have h3 : ∫ y, ‖f y - m‖ ^ 3 ∂μ ≤ ∫ y, 4 * (‖f y‖ ^ 3 + ‖m‖ ^ 3) ∂μ :=
    integral_mono_of_nonneg (ae_of_all _ fun y => by positivity)
      ((hn3.add (integrable_const _)).const_mul _)
      (ae_of_all _ fun y => by
        refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 3).trans ?_
        exact cube_add_le (norm_nonneg _) (norm_nonneg _))
  rw [integral_const_mul, integral_add hn3 (integrable_const _)] at h3
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h3
  linarith

end RandomInitial

end HRS
