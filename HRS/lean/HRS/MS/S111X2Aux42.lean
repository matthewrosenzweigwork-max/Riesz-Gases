import HRS.MS.S111X2Aux41
import HRS.MS.S111X2Aux40
import HRS.MS.S111BDAux4
import HRS.MS.R2InterpAux5

/-!
# S11.1 X2, packet H02 (part 4): second moments of the projected Gaussian window

For a window `W` of the linear Gaussian evolution: `E M(P_L W, P_L W) = ∑_{p,q} σ_{pq} M(b_p,b_q)` with `σ_{pq} = E[ℓ_p(W)ℓ_q(W)]`
the covariance entries `linearGaussianCov`; the `2×2` covariance matrices are positive semidefinite (previous part), so the
mixed second moment of the Gaussian vector is its covariance entry.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole HRS.MS.R2Interp

variable {d : ℕ} {m T : ℝ}

theorem s111x2_gauss_mixed {q : ℕ} (S : Matrix (Fin q) (Fin q) ℝ) (hS : S.PosSemidef) (i j : Fin q) :
    ∫ x, x i * x j ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) S) = S i j := by
  haveI : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) S) := inferInstance
  have hmem : ∀ k : Fin q, MemLp (fun x : EuclideanSpace ℝ (Fin q) => x k) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) S) := fun k =>
    ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).comp_memLp' IsGaussian.memLp_two_id)
  have hmean : ∀ k : Fin q, ∫ x, x k ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) S) = 0 := by
    intro k
    have := (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).integral_comp_id_comm
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) S) IsGaussian.integrable_id
    simpa using this
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin q))) hS i j
  rw [covariance_eq_sub (hmem i) (hmem j)] at h
  simp only [Pi.mul_apply] at h
  have h1 := hmean i
  have h2 := hmean j
  simp only [h1, h2, mul_zero, sub_zero] at h
  exact h

/-- Expectation of a quadratic form of the projected path. -/
theorem s111x2_exp_expand (hT : 0 < T) (L : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : Ω → OscPath d m T) (hL2 : MemLp W 2 P) (M : OscPath d m T [×2]→L[ℝ] ℝ)
    (σ : ℕ × MultiIndex d → ℕ × MultiIndex d → ℝ)
    (hσ : ∀ p ∈ s102_idx d L, ∀ q ∈ s102_idx d L,
      ∫ ζ, s102_ellp hT L p (W ζ) * s102_ellp hT L q (W ζ) ∂P = σ p q) :
    ∫ ζ, M ![s102_Pj T hT L (W ζ), s102_Pj T hT L (W ζ)] ∂P =
      ∑ p ∈ s102_idx d L, ∑ q ∈ s102_idx d L, σ p q * M ![s102_bpath (m := m) T L p, s102_bpath (m := m) T L q] := by
  classical
  have hint : ∀ p q, Integrable (fun ζ => s102_ellp hT L p (W ζ) * s102_ellp hT L q (W ζ)) P := fun p q =>
    ((s102_ellp hT L p).comp_memLp' hL2).integrable_mul ((s102_ellp hT L q).comp_memLp' hL2)
  have hpt : ∀ ζ, M ![s102_Pj T hT L (W ζ), s102_Pj T hT L (W ζ)] =
      ∑ p ∈ s102_idx d L, ∑ q ∈ s102_idx d L, s102_ellp hT L p (W ζ) * s102_ellp hT L q (W ζ) *
        M ![s102_bpath (m := m) T L p, s102_bpath (m := m) T L q] := by
    intro ζ
    rw [s102_Pj_decomp hT L (W ζ)]
    exact s111x2_bil_expand M _ _ _ _
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (hint p q).mul_const _))]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [integral_finsetSum _ (fun q _ => (hint p q).mul_const _)]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_mul_const, hσ p hp q hq]

end HRS.MS.S111X2
