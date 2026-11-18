import HRS.MS.LcFlowAux1
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# UL-2, part 1: the Ornstein-Uhlenbeck covariance `ouCov`, the law `ouLaw` and the base semigroup `ouSg`

Setting (supplement S5.1, `W:r2:ou-smoothing`; infrastructure packet UL-2, not a manuscript row).
`Q` is a real `d × d` matrix (acting as `lcQ Q`), `ν ≥ 0` a constant viscosity, and
`E_v = e^{-vQ}` (`ouExp`).  The OU covariance of the solution of `dX = -QX dt + √(2ν) dW`
started at `0` after time `τ ≥ 0` is `Σ_τ = 2ν ∫_0^τ E_v E_vᵀ dv`.

Definitions.
* `ouExp Q v = e^{-vQ}` (continuous linear map of `Euc d`).
* `ouCov Q ν τ : Matrix (Fin d) (Fin d) ℝ`, the matrix with entries
  `2ν ∫_0^τ ⟪E_vᵀ e_i, E_vᵀ e_j⟫ dv`, i.e. the `(i,j)` entry of `2ν ∫_0^τ E_v E_vᵀ dv`
  (`E_vᵀ` is `ContinuousLinearMap.adjoint (ouExp Q v) = e^{-vQᵀ}`, `ul2_adj_eq`).
* `ouLaw Q ν τ := multivariateGaussian 0 (ouCov Q ν τ)`: the law `N(0, Σ_τ)`; by definition of
  Mathlib's `multivariateGaussian` it is the image of the standard Gaussian `stdGaussian (Euc d)`
  under `x ↦ Σ_τ^{1/2} x` (`ouLaw_eq_map`), which is the form UL-3 needs instead of a density
  (Mathlib has no density formula for `multivariateGaussian`).
* `ouSg Q ν τ h x = ∫ h (e^{-τQ} x + y) d ouLaw Q ν τ (y)`.

Results.
* `ouCov_quad`: `⟨ξ, Σ_τ ξ⟩ = 2ν ∫_0^τ |E_vᵀ ξ|² dv`; `ouCov_posSemidef` (`ν, τ ≥ 0`), `ouCov_posDef`
  (`ν, τ > 0`), `ouCov_bounds` (`0 < ν`, `T`): `λ τ |ξ|² ≤ ⟨ξ,Σ_τ ξ⟩ ≤ Λ τ |ξ|²` for `τ ∈ [0,T]`.
* `ou_charFun`: `charFun (ouLaw Q ν τ) ξ = exp(-⟨ξ, Σ_τ ξ⟩/2)` and the integral form.

Hypotheses: `ν ≥ 0`, `τ ≥ 0` where needed for positive semidefiniteness (for other values
`multivariateGaussian` silently returns a Dirac mass, so these hypotheses are not removable).
Helper lemmas carry the prefix `ul2_`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped InnerProduct Matrix

noncomputable section

namespace HRS.MS.Ul

open HRS HRS.MS.Lc

variable {d : ℕ}

/-! ### Definitions -/

/-- `E_v = e^{-vQ}`. -/
def ouExp (Q : Matrix (Fin d) (Fin d) ℝ) (v : ℝ) : Euc d →L[ℝ] Euc d :=
  NormedSpace.exp ((-v) • lcQ Q)

/-- The OU covariance `Σ_τ = 2ν ∫_0^τ e^{-vQ} e^{-vQᵀ} dv`, entrywise
`2ν ∫_0^τ ⟪(e^{-vQ})ᵀ e_i, (e^{-vQ})ᵀ e_j⟫ dv`. -/
def ouCov (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => 2 * ν * ∫ v in (0 : ℝ)..τ,
    inner ℝ (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ)))

/-- The OU law `N(0, Σ_τ)` of the noise-driven part of the OU process after time `τ`. -/
def ouLaw (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) : Measure (Euc d) :=
  multivariateGaussian 0 (ouCov Q ν τ)

/-- The base (Ornstein-Uhlenbeck, Mehler) semigroup `P_τ h(x) = ∫ h(e^{-τQ} x + y) dN(0,Σ_τ)(y)`. -/
def ouSg (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, h ((ouExp Q τ) x + y) ∂(ouLaw Q ν τ)

instance ouLaw_isProbabilityMeasure (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) :
    IsProbabilityMeasure (ouLaw Q ν τ) := by
  unfold ouLaw; infer_instance

instance ouLaw_isGaussian (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) : IsGaussian (ouLaw Q ν τ) := by
  unfold ouLaw; infer_instance

open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- `ouLaw` is the image of the standard Gaussian under the square root of the covariance. -/
theorem ouLaw_eq_map (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) :
    ouLaw Q ν τ = (stdGaussian (EuclideanSpace ℝ (Fin d))).map
      (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ)) x) := by
  unfold ouLaw multivariateGaussian
  simp

/-- The mean of `ouLaw` is `0`. -/
theorem ouLaw_integral_id (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) :
    ∫ y, y ∂(ouLaw Q ν τ) = 0 := by
  unfold ouLaw; exact integral_id_multivariateGaussian

/-! ### The exponential and its adjoint -/

theorem ul2_exp_cont (Q : Matrix (Fin d) (Fin d) ℝ) : Continuous (ouExp Q) :=
  NormedSpace.exp_continuous.comp (continuous_neg.smul continuous_const)

theorem ouExp_zero (Q : Matrix (Fin d) (Fin d) ℝ) : ouExp Q 0 = 1 := by
  rw [ouExp, neg_zero, zero_smul ℝ (lcQ Q), NormedSpace.exp_zero]

theorem ul2_exp_mul_neg (Q : Matrix (Fin d) (Fin d) ℝ) (v : ℝ) : ouExp Q v * ouExp Q (-v) = 1 := by
  unfold ouExp
  have := lc1_exp_cancel Q v
  rwa [neg_neg]

theorem ul2_adj_cont (Q : Matrix (Fin d) (Fin d) ℝ) (ξ : Euc d) :
    Continuous fun v => ContinuousLinearMap.adjoint (ouExp Q v) ξ :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euc d) (F := Euc d)).continuous.comp
    (ul2_exp_cont Q)).clm_apply continuous_const

/-- `(e^{-vQ})ᵀ = e^{-vQᵀ}`. -/
theorem ul2_adj_eq (Q : Matrix (Fin d) (Fin d) ℝ) (v : ℝ) :
    ContinuousLinearMap.adjoint (ouExp Q v) = NormedSpace.exp ((-v) • star (lcQ Q)) := by
  rw [← ContinuousLinearMap.star_eq_adjoint]
  unfold ouExp
  rw [NormedSpace.star_exp, star_smul, star_neg, star_trivial]

/-- `Σ_i Σ_j ξ_i ξ_j ⟪T e_i, T e_j⟫ = |T ξ|²`. -/
theorem ul2_sum_inner (T : Euc d →L[ℝ] Euc d) (ξ : Euc d) :
    ∑ i, ∑ j, ξ i * ξ j * inner ℝ (T (EuclideanSpace.single i (1 : ℝ)))
      (T (EuclideanSpace.single j (1 : ℝ))) = ‖T ξ‖ ^ 2 := by
  have hξ : ξ = ∑ i, ξ i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr' ξ
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left] using this.symm
  have hT : T ξ = ∑ i, ξ i • T (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hξ]
    simp [map_sum]
  rw [← real_inner_self_eq_norm_sq, hT, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-! ### The quadratic form of `ouCov` -/

theorem ul2_integrand_cont (Q : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    Continuous fun v => inner ℝ
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ))) :=
  (ul2_adj_cont Q _).inner (ul2_adj_cont Q _)

/-- `⟨ξ, Σ_τ ξ⟩ = 2ν ∫_0^τ |e^{-vQᵀ} ξ|² dv`. -/
theorem ouCov_quad (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) (ξ : Euc d) :
    ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ =
      2 * ν * ∫ v in (0 : ℝ)..τ, ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 := by
  have hI : ∀ i j, IntervalIntegrable (fun v => ξ i * ξ j * inner ℝ
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ)))) volume 0 τ :=
    fun i j => (continuous_const.mul (ul2_integrand_cont Q i j)).intervalIntegrable _ _
  have hI2 : ∀ i, IntervalIntegrable (fun v => ∑ j, ξ i * ξ j * inner ℝ
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ)))) volume 0 τ :=
    fun i => (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (ul2_integrand_cont Q i j)).intervalIntegrable _ _
  have e1 : ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ = 2 * ν * ∑ i, ∑ j, ∫ v in (0 : ℝ)..τ, ξ i * ξ j * inner ℝ
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ))) := by
    simp only [dotProduct, Matrix.mulVec, ouCov, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [e1]
  congr 1
  have e2 : ∀ i, ∑ j, ∫ v in (0 : ℝ)..τ, ξ i * ξ j * inner ℝ
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ))) =
      ∫ v in (0 : ℝ)..τ, ∑ j, ξ i * ξ j * inner ℝ
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint (ouExp Q v) (EuclideanSpace.single j (1 : ℝ))) := fun i =>
    (intervalIntegral.integral_finsetSum fun j _ => hI i j).symm
  simp_rw [e2]
  rw [← intervalIntegral.integral_finsetSum fun i _ => hI2 i]
  refine intervalIntegral.integral_congr fun v _ => ?_
  exact ul2_sum_inner _ ξ

theorem ouCov_isHermitian (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) : (ouCov Q ν τ).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [ouCov, Matrix.of_apply, star_trivial]
  simp_rw [real_inner_comm]

theorem ouCov_posSemidef (Q : Matrix (Fin d) (Fin d) ℝ) {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    (ouCov Q ν τ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨ouCov_isHermitian Q ν τ, fun x => ?_⟩
  have h := ouCov_quad Q ν τ (WithLp.toLp 2 x)
  simp only [star_trivial]
  have h2 : (WithLp.toLp 2 x : Euc d).ofLp = x := rfl
  rw [h2] at h
  rw [h]
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hτ fun v _ => by positivity)

/-! ### Two-sided bounds -/

/-- Compactness bound: `‖e^{-vQ}‖ ≤ K` for `|v| ≤ T`. -/
theorem ul2_exp_bound (Q : Matrix (Fin d) (Fin d) ℝ) (T : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ v : ℝ, |v| ≤ T → ‖ouExp Q v‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    (ul2_exp_cont Q).continuousOn
  refine ⟨max K 1, le_max_right _ _, fun v hv => ?_⟩
  exact (hK v (abs_le.mp hv)).trans (le_max_left _ _)

theorem ul2_adj_upper (Q : Matrix (Fin d) (Fin d) ℝ) {K T : ℝ} (hK : ∀ v : ℝ, |v| ≤ T → ‖ouExp Q v‖ ≤ K)
    {v : ℝ} (hv : |v| ≤ T) (ξ : Euc d) :
    ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ≤ K * ‖ξ‖ := by
  refine ((ContinuousLinearMap.adjoint (ouExp Q v)).le_opNorm ξ).trans ?_
  rw [LinearIsometryEquiv.norm_map]
  exact mul_le_mul_of_nonneg_right (hK v hv) (norm_nonneg _)

theorem ul2_adj_lower (Q : Matrix (Fin d) (Fin d) ℝ) {K T : ℝ} (hK : ∀ v : ℝ, |v| ≤ T → ‖ouExp Q v‖ ≤ K)
    {v : ℝ} (hv : |v| ≤ T) (ξ : Euc d) :
    ‖ξ‖ ≤ K * ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ := by
  have h1 : ContinuousLinearMap.adjoint (ouExp Q (-v)) (ContinuousLinearMap.adjoint (ouExp Q v) ξ) =
      ξ := by
    have h0 : star (ouExp Q v * ouExp Q (-v)) = 1 := by rw [ul2_exp_mul_neg, star_one]
    rw [star_mul] at h0
    have := congrArg (fun A : Euc d →L[ℝ] Euc d => A ξ) h0
    simpa [ContinuousLinearMap.star_eq_adjoint] using this
  have h2 := ul2_adj_upper Q hK (v := -v) (by rwa [abs_neg]) (ContinuousLinearMap.adjoint (ouExp Q v) ξ)
  rwa [h1] at h2

/-- **Covariance bounds.**  For `ν > 0` and `T`, there are `0 < λ`, `Λ` with
`λ τ |ξ|² ≤ ⟨ξ, Σ_τ ξ⟩ ≤ Λ τ |ξ|²` for all `τ ∈ [0,T]`, `ξ`. -/
theorem ouCov_bounds (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) :
    ∃ lam Lam : ℝ, 0 < lam ∧ 0 < Lam ∧ ∀ τ ∈ Icc (0 : ℝ) T, ∀ ξ : Euc d,
      lam * τ * ‖ξ‖ ^ 2 ≤ ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ ∧
      ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ ≤ Lam * τ * ‖ξ‖ ^ 2 := by
  obtain ⟨K, hK1, hK⟩ := ul2_exp_bound Q T
  have hK0 : 0 < K := by linarith
  refine ⟨2 * ν / K ^ 2, 2 * ν * K ^ 2, by positivity, by positivity, fun τ hτ ξ => ?_⟩
  rw [ouCov_quad]
  have hvT : ∀ v ∈ Icc (0 : ℝ) τ, |v| ≤ T := fun v hv => by
    rw [abs_of_nonneg hv.1]; exact hv.2.trans hτ.2
  have hc : Continuous fun v => ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 :=
    (ul2_adj_cont Q ξ).norm.pow 2
  have hint : IntervalIntegrable (fun v => ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2)
      volume 0 τ := hc.intervalIntegrable _ _
  constructor
  · have : ∫ v in (0 : ℝ)..τ, (‖ξ‖ / K) ^ 2 ≤
        ∫ v in (0 : ℝ)..τ, ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on hτ.1 (by simp) hint fun v hv => ?_
      have := ul2_adj_lower Q hK (hvT v hv) ξ
      have h3 : ‖ξ‖ / K ≤ ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ := by
        rw [div_le_iff₀ hK0]; linarith
      exact pow_le_pow_left₀ (by positivity) h3 2
    have e : ∫ v in (0 : ℝ)..τ, (‖ξ‖ / K) ^ 2 = τ * (‖ξ‖ / K) ^ 2 := by simp
    rw [e] at this
    have : 2 * ν / K ^ 2 * τ * ‖ξ‖ ^ 2 = 2 * ν * (τ * (‖ξ‖ / K) ^ 2) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left ‹_› (by positivity)
  · have : ∫ v in (0 : ℝ)..τ, ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 ≤
        ∫ v in (0 : ℝ)..τ, (K * ‖ξ‖) ^ 2 := by
      refine intervalIntegral.integral_mono_on hτ.1 hint (by simp) fun v hv => ?_
      exact pow_le_pow_left₀ (norm_nonneg _) (ul2_adj_upper Q hK (hvT v hv) ξ) 2
    have e : ∫ v in (0 : ℝ)..τ, (K * ‖ξ‖) ^ 2 = τ * (K * ‖ξ‖) ^ 2 := by simp
    rw [e] at this
    have : 2 * ν * K ^ 2 * τ * ‖ξ‖ ^ 2 = 2 * ν * (τ * (K * ‖ξ‖) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left ‹_› (by positivity)

/-- `Σ_τ` is positive definite for `ν, τ > 0`. -/
theorem ouCov_posDef (Q : Matrix (Fin d) (Fin d) ℝ) {ν τ : ℝ} (hν : 0 < ν) (hτ : 0 < τ) :
    (ouCov Q ν τ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨ouCov_isHermitian Q ν τ, fun x hx => ?_⟩
  obtain ⟨lam, Lam, hlam, -, h⟩ := ouCov_bounds Q hν τ
  have hx' : (WithLp.toLp 2 x : Euc d) ≠ 0 := fun h0 => hx (by simpa using congrArg WithLp.ofLp h0)
  have := (h τ ⟨hτ.le, le_rfl⟩ (WithLp.toLp 2 x)).1
  have h2 : (WithLp.toLp 2 x : Euc d).ofLp = x := rfl
  rw [h2] at this
  simp only [star_trivial]
  refine lt_of_lt_of_le ?_ this
  have : 0 < ‖(WithLp.toLp 2 x : Euc d)‖ := norm_pos_iff.2 hx'
  positivity

/-! ### Characteristic function -/

/-- **`ou_charFun`.**  `charFun (ouLaw Q ν τ) ξ = exp(-⟨ξ, Σ_τ ξ⟩ / 2)` for `ν, τ ≥ 0`. -/
theorem ou_charFun (Q : Matrix (Fin d) (Fin d) ℝ) {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (ξ : Euc d) :
    charFun (ouLaw Q ν τ) ξ = Complex.exp (-(((ξ ⬝ᵥ ouCov Q ν τ *ᵥ ξ : ℝ) : ℂ) / 2)) := by
  unfold ouLaw
  rw [charFun_multivariateGaussian (ouCov_posSemidef Q hν hτ)]
  simp

/-- Integral form: `charFun (ouLaw Q ν τ) ξ = exp(-ν ∫_0^τ |e^{-vQᵀ} ξ|² dv)`. -/
theorem ou_charFun_integral (Q : Matrix (Fin d) (Fin d) ℝ) {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ)
    (ξ : Euc d) :
    charFun (ouLaw Q ν τ) ξ = Complex.exp (-((ν * ∫ v in (0 : ℝ)..τ,
      ‖ContinuousLinearMap.adjoint (ouExp Q v) ξ‖ ^ 2 : ℝ) : ℂ)) := by
  rw [ou_charFun Q hν hτ, ouCov_quad]
  congr 1
  push_cast
  ring

end HRS.MS.Ul
