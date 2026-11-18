import HRS.Prob.Metrics

/-!
# S21H (packet H of `docs/S21_PLAN.md`): the `W_1` half of the open input `S21Init` -- plan and part 1

## Verdict (checked against the supplement, L3589-3601 "explicit Wasserstein estimate", and L5143-5160)
The target is TRUE and non-vacuous; no frozen statement is touched.  Exponent arithmetic: projection tails `R^{-3/4}` (both laws), Gaussian smoothing
of a unit Lipschitz function in `ℝ^p`, `p = O(R²)`: value cost `ε √p = ε R`, Hessian `≤ 1/ε` (dimension free), static comparison
`√δ (1 + 1/ε)`; with `R = δ^{-1/5}`, `ε = δ^{7/20}` all three terms are `δ^{3/20}` (`s21h_rate_alg`).
The merged `dc2_to_w1` (Lemma A.26) has the dimension-dependent Hessian bound `√p/ε` and would only give `δ^{3/28}`; hence part 1 below.

Junk-value audit: all hypotheses are `MemLp id 2` (second moments) and `lintegral` tails (so integrability is part of the claim); `wassersteinE` is
`ℝ≥0∞`-valued with an `ofReal` bound, `δ ∈ (0,1]`, rpow of positive bases; no `Measure.map` of a non-measurable map (all maps are continuous
linear or the measurable `featureVec`); `d ≥ 2` and `β > 0` as in S21 (the `β < 1` scaling is packet K).

## Interface with packet G (important)
`S21InitAt` asks for ONE `γ₀` with fdd, smooth and `W_1` clauses; the smooth metric on `C_b²(X)` cannot test unbounded Lipschitz functions and the
weighted cosine coordinates have unbounded operator norm `X → ℓ²` as the rank grows, so `W_1` is derived from the rank-uniform DERIVATIVE-ONLY static
comparison on `ℓ²` (4th conjunct of `StaticFieldConclusion`, `quadratic_static_field_proof`).  Hence `s21h_init_w1` (WsInitHAux9) is a conditional
theorem for `γ₀ = ι_* γ̃` where packet G supplies: the bounded `ι : ℓ² → OscPath d m T`, a summable `C_b^J` orbit family `φ`, the centred Gaussian
`γ̃` on `ℓ²` with the susceptibility covariance, the representation `s21IP x = ι (featureVec φ m_N x)` and the box decay of the cb-norms
`∀ Q ≥ 1, ∃ I, |I| ≤ K Q², ∑_{k ∉ I} ‖φ_k‖²_{C_b^J} ≤ τ₀² Q^{-3/2}`.  Everything else (static comparison, variance of linear statistics, covariance
bound `C(f,f) ≤ 4‖f‖²_∞`, smoothing, projection, triangle inequality) is proved here and uses merged results only.

## Files (all new, namespace `HRS.MS.S21`, helpers `s21h_`; compiled with `tools/wcheck.sh`)
* `WsInitHAux1`: `s21h_second_moment_inner`, `s21h_integral_abs_fderiv_kernel_le`, `s21h_norm_fderiv_fderiv_gsmooth_le` (`‖D² gsmooth‖ ≤ 1/ε`).
* `WsInitHAux2`: `S21hDerivComp`, `s21h_smooth_approx`, `s21h_test_bound`, `s21h_w1_coord` (`W_1^{ℝ^p}(c_*μ, c_*γ) ≤ 2ε√p + η(A₁ + A₂/ε)`).
* `WsInitHAux3`: `s21h_rate_alg`, `s21h_leg_tail`, `s21h_w1_abstract` (rate `δ^{3/20}` from coordinate projections `c, e` with tails).
* `WsInitHAux4`: `s21h_scheme_of_subspace`, `s21h_w1_of_subspaces` (projections onto finite-dimensional subspaces of a Hilbert space).
* `WsInitHAux5`: `ℓ²` coordinate projections, `s21h_tail_of_coords` (tails from coordinate second moments).
* `WsInitHAux6`: `s21h_w1_of_coords`, `s21h_derivComp_of_static`, `s21h_init_w1` (feature law of any `P` with `StaticFieldConclusion`).
* `WsInitHAux7`: `s21h_cov_le`, `s21h_gauss_coord`, `s21h_particle_coord` (coordinate second moments of the Gaussian and of the Gibbs feature law).
* `WsInitHAux8`: `s21h_init_w1_stat` (stationary Gibbs law, all static inputs from merged theorems).
* `WsInitHAux9`: `s21h_init_w1`, `s21h_init_w1_unif` (S21 shape: `s21IP`, `meanEmpirical`, `OscPath`).
* `WsInitHAux10-12`: `s21h_levelset`, `s21h_tail_nat`, `s21h_box_of_product`, `s21h_box_osc` (box decomposition from the product decay
  `‖φ_k‖_{C_b^J} ≤ A (1+n)^{-5/4} λ_α^{-γ}`, `5d/4 < γ`).
* `WsInitHAux13`: `s21h_w1_half` (final: fixed orbit family `φ`, `ι`, `γ̃`; `∃ C_W` independent of `N`, `W_1 ≤ C_W δ_N^{3/20}` whenever
  `s21IP = ι ∘ featureVec φ m_N`).  Remaining for S2.1(i) (packet G, plus gluing): `ι`, `φ`, `γ̃` with `hpath`, the decay `hdecay` with
  `γ = (m - I)/2` where `m - I > 5d/2` (arithmetic on `s52bIdx`), the fdd/PSD clauses and the smooth clause; then `S21InitAt` follows.

## Part 1 (this file)
For `f : ℝ^p → ℝ` bounded, continuous and 1-Lipschitz, the Gaussian smoothing `gsmooth ε f` of `HRS/Prob/Metrics.lean` satisfies
`‖D² gsmooth ε f‖ ≤ 1/ε`, with NO dependence on `p` (the merged `norm_fderiv_fderiv_gsmooth_le` gives `√p/ε`): for the directional derivative
`D_u gsmooth ε f (x) = ∫ f(x-z) D_uκ(z) dz` the difference quotient in `x` is bounded by `|x-x'| ∫ |D_uκ| ≤ |x-x'| ‖u‖/ε`, since
`∫ |⟨z,u⟩| κ_ε(z) dz ≤ ε ‖u‖` (Cauchy-Schwarz and the covariance of the Gaussian in the direction `u`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

variable {p : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin p)

/-- The second moment of a Gaussian `N(0, ε² I)` in the direction `u`. -/
theorem s21h_second_moment_inner {ε : ℝ} (hε : 0 < ε) (u : 𝔼) :
    ∫ z, (inner ℝ u z) ^ 2 ∂(multivariateGaussian (0 : 𝔼) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ))) =
      ε ^ 2 * ‖u‖ ^ 2 := by
  set S : Matrix (Fin p) (Fin p) ℝ := ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) with hS
  have hpsd : S.PosSemidef := Matrix.PosSemidef.one.smul (by positivity)
  set γ := multivariateGaussian (0 : 𝔼) S with hγ
  have hm : MemLp id 2 γ := IsGaussian.memLp_two_id
  have h1 := covarianceBilin_apply (μ := γ) hm u u
  have h2 := covarianceBilin_multivariateGaussian (μ := (0 : 𝔼)) hpsd u u
  have hmean : γ[id] = 0 := by simp [hγ]
  rw [hmean] at h1
  simp only [sub_zero] at h1
  have h3 : ∫ z, (inner ℝ u z) ^ 2 ∂γ = ∫ z, inner ℝ u z * inner ℝ u z ∂γ :=
    integral_congr_ae (ae_of_all _ fun z => by ring)
  rw [h3, ← h1, hγ, h2]
  simp only [hS, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

/-- `∫ κ_ε(z) |⟨z,u⟩| dz ≤ ε ‖u‖`. -/
theorem s21h_integral_kernel_abs_inner_le {ε : ℝ} (hε : 0 < ε) (u : 𝔼) :
    ∫ z, gaussKernel p (1 / (2 * ε ^ 2)) z * |inner ℝ z u| ≤ ε * ‖u‖ := by
  rw [integral_kernel_eq_mvG hε (fun z : 𝔼 => |inner ℝ z u|)]
  set γ := multivariateGaussian (0 : 𝔼) (ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ)) with hγ
  have hm : MemLp (fun z : 𝔼 => |inner ℝ z u|) 2 γ := by
    have h1 : MemLp (fun z : 𝔼 => inner ℝ u z) 2 γ :=
      (innerSL ℝ u).comp_memLp' (IsGaussian.memLp_two_id (μ := γ))
    have h2 := h1.norm
    have e : (fun z : 𝔼 => |inner ℝ z u|) = fun z : 𝔼 => ‖inner ℝ u z‖ := by
      funext z; simp [real_inner_comm]
    rw [e]; exact h2
  refine (integral_le_sqrt γ hm).trans ?_
  have : ∫ z, |inner ℝ z u| ^ 2 ∂γ = ε ^ 2 * ‖u‖ ^ 2 := by
    rw [← s21h_second_moment_inner hε u]
    exact integral_congr_ae (ae_of_all _ fun z => by simp [sq_abs, real_inner_comm])
  rw [this, show ε ^ 2 * ‖u‖ ^ 2 = (ε * ‖u‖) ^ 2 by ring]
  exact (Real.sqrt_sq (by positivity)).le


/-- `∫ |D_uκ_ε| ≤ ‖u‖/ε`. -/
theorem s21h_integral_abs_fderiv_kernel_le {ε : ℝ} (hε : 0 < ε) (u : 𝔼) :
    ∫ z, |fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) z u| ≤ ‖u‖ / ε := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  have e : ∀ z : 𝔼, |fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) z u| =
      (1 / ε ^ 2) * (gaussKernel p (1 / (2 * ε ^ 2)) z * |inner ℝ z u|) := by
    intro z
    rw [fderiv_gaussKernel]
    have hK := gaussKernel_pos hb z
    have h0 : (((-2 * (1 / (2 * ε ^ 2)) * gaussKernel p (1 / (2 * ε ^ 2)) z) • ipCLM p z : 𝔼 →L[ℝ] ℝ) u) =
        (-2 * (1 / (2 * ε ^ 2)) * gaussKernel p (1 / (2 * ε ^ 2)) z) * inner ℝ z u := rfl
    rw [h0, abs_mul]
    have h2 : |(-2 * (1 / (2 * ε ^ 2)) * gaussKernel p (1 / (2 * ε ^ 2)) z)| =
        (1 / ε ^ 2) * gaussKernel p (1 / (2 * ε ^ 2)) z := by
      rw [abs_of_neg (by nlinarith [hK] : -2 * (1 / (2 * ε ^ 2)) * gaussKernel p (1 / (2 * ε ^ 2)) z < 0)]
      field_simp
    rw [h2]; ring
  simp_rw [e]
  rw [integral_const_mul]
  calc 1 / ε ^ 2 * ∫ z, gaussKernel p (1 / (2 * ε ^ 2)) z * |inner ℝ z u| ≤ 1 / ε ^ 2 * (ε * ‖u‖) := by
        gcongr; exact s21h_integral_kernel_abs_inner_le hε u
    _ = ‖u‖ / ε := by field_simp

/-- Dimension-free Hessian bound for the Gaussian smoothing of a bounded 1-Lipschitz function: `‖D² g‖ ≤ 1/ε`
(the merged `norm_fderiv_fderiv_gsmooth_le` has `√p/ε`). -/
theorem s21h_norm_fderiv_fderiv_gsmooth_le {ε : ℝ} (hε : 0 < ε) {f : 𝔼 → ℝ} (hf : Continuous f) {R : ℝ}
    (hR : ∀ y, |f y| ≤ R) (hL : LipschitzWith 1 f) (x : 𝔼) :
    ‖fderiv ℝ (fderiv ℝ (gsmooth ε f)) x‖ ≤ 1 / ε := by
  have hb : 0 < 1 / (2 * ε ^ 2) := by positivity
  rw [fderiv_gsmooth hε hf hR]
  refine norm_fderiv_le_of_lip' ℝ (by positivity) (Filter.Eventually.of_forall fun x' => ?_)
  set κ' := fderiv ℝ (gaussKernel p (1 / (2 * ε ^ 2))) with hκ'
  have hκc : Continuous κ' := (contDiff_gaussKernel (p := p) _).continuous_fderiv (by simp)
  have hκi : Integrable κ' := integrable_fderiv_gaussKernel (p := p) hb
  rw [conv_comm f κ' x', conv_comm f κ' x]
  have i1 : Integrable (fun z => f (x' - z) • κ' z) :=
    integrable_bdd_smul (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _) hκc hκi
  have i2 : Integrable (fun z => f (x - z) • κ' z) :=
    integrable_bdd_smul (hf.comp (continuous_const.sub continuous_id)) (fun z => hR _) hκc hκi
  rw [← integral_sub i1 i2]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have i3 : Integrable (fun z => f (x' - z) • κ' z - f (x - z) • κ' z) := i1.sub i2
  rw [ContinuousLinearMap.integral_apply i3 u]
  have hu : Integrable (fun z => κ' z u) :=
    ((ContinuousLinearMap.apply ℝ ℝ u).integrable_comp hκi)
  refine (norm_integral_le_of_norm_le (hu.norm.const_mul (‖x' - x‖)) (ae_of_all _ fun z => ?_)).trans ?_
  · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ← sub_mul,
      norm_mul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := hL.dist_le_mul (x' - z) (x - z)
    simpa [Real.dist_eq, dist_eq_norm] using this
  · rw [integral_const_mul]
    have := s21h_integral_abs_fderiv_kernel_le hε u
    simp only [Real.norm_eq_abs]
    calc ‖x' - x‖ * ∫ z, |κ' z u| ≤ ‖x' - x‖ * (‖u‖ / ε) := by gcongr
      _ = 1 / ε * ‖x' - x‖ * ‖u‖ := by ring

end HRS.MS.S21
