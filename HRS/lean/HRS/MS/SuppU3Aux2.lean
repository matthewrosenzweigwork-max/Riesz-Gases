import HRS.MS.SuppU3Aux1

/-!
# U3, part 2: mollification of a Hilbert-valued map with weak derivative bounds

`u3_moll φ Φ = ρ ⋆ Φ` with `ρ = φ.normed volume` (a `ContDiffBump`).  If `Φ : ℝ^d → H` is continuous and the
scalar functions `ℓ_i ∘ Φ` (for a norming family `ℓ_i`) are `C^m` with `‖D^k(ℓ_i ∘ Φ)‖ ≤ B nrm_i`, then
`D^k(ρ ⋆ Φ)` has operator norm `≤ B` for `k ≤ m` (uniformly in the radius of the bump).
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff Convolution

namespace HRS.MS.SuppU3

variable {d : ℕ}

section Moll
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The mollification `ρ ⋆ Φ`. -/
def u3_moll (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (Φ : EuclideanSpace ℝ (Fin d) → H)
    (y : EuclideanSpace ℝ (Fin d)) : H :=
  ∫ t, φ.normed volume t • Φ (y - t)

theorem u3_moll_eq (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (Φ : EuclideanSpace ℝ (Fin d) → H) :
    u3_moll φ Φ = (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Φ) := by
  funext y; rw [convolution_lsmul]; rfl

theorem u3_moll_contDiff (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (Φ : EuclideanSpace ℝ (Fin d) → H) (hΦ : Continuous Φ) : ContDiff ℝ ∞ (u3_moll φ Φ) := by
  rw [u3_moll_eq]
  exact φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.contDiff_normed hΦ.locallyIntegrable

theorem u3_moll_dist (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (Φ : EuclideanSpace ℝ (Fin d) → H) (hΦ : Continuous Φ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (x : EuclideanSpace ℝ (Fin d)) :
    ‖u3_moll φ Φ x - Φ x‖ ≤ L * φ.rOut := by
  have h := dist_convolution_le (μ := volume) (f := φ.normed volume) (x₀ := x) (R := φ.rOut)
    (ε := L * φ.rOut) (z₀ := Φ x) (g := Φ) (mul_nonneg hL0 (by have := φ.rIn_pos; have := φ.rIn_lt_rOut; linarith))
    (by rw [φ.support_normed_eq]) φ.nonneg_normed φ.integral_normed hΦ.aestronglyMeasurable
    (fun y hy => by
      rw [dist_eq_norm]
      refine (hL y x).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hL0
      rw [mem_ball, dist_eq_norm] at hy; exact hy.le)
  rw [← u3_moll_eq, dist_eq_norm] at h
  exact h

variable {ι : Type*} (ℓ : ι → H →L[ℝ] ℝ) (nrm : ι → ℝ)

theorem u3_moll_bound (hnorm : ∀ (F : H) (c : ℝ), 0 ≤ c → (∀ i, |ℓ i F| ≤ c * nrm i) → ‖F‖ ≤ c)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d))) (hφ : φ.rOut ≤ 1)
    (Φ : EuclideanSpace ℝ (Fin d) → H) (hΦ : Continuous Φ) (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hΦm : ∀ i, ContDiff ℝ m (fun x => ℓ i (Φ x)))
    (hΦb : ∀ i, ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k (fun x => ℓ i (Φ x)) x‖ ≤ B * nrm i)
    (k : ℕ) (hk : k ≤ m) (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ k (u3_moll φ Φ) x‖ ≤ B := by
  have hsm := u3_moll_contDiff φ Φ hΦ
  refine ContinuousMultilinearMap.opNorm_le_bound hB (fun v => ?_)
  refine hnorm _ _ (by positivity) (fun i => ?_)
  -- the composite with `ℓ i`
  have hcomp : (ℓ i) ∘ (u3_moll φ Φ) = fun y => ∫ t, φ.normed volume t • (ℓ i (Φ (y - t))) := by
    funext y
    simp only [Function.comp_apply, u3_moll]
    have hint : Integrable (fun t => φ.normed volume t • Φ (y - t)) volume :=
      φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
        (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed.locallyIntegrable (μ := volume)) hΦ y
    rw [← ContinuousLinearMap.integral_comp_comm (ℓ i) hint]
    simp
  have h1 : iteratedFDeriv ℝ k ((ℓ i) ∘ (u3_moll φ Φ)) x =
      (ℓ i).compContinuousMultilinearMap (iteratedFDeriv ℝ k (u3_moll φ Φ) x) :=
    (ℓ i).iteratedFDeriv_comp_left (hsm.contDiffAt.of_le (by exact_mod_cast le_top)) le_rfl
  have h2 : iteratedFDeriv ℝ k (fun y => ∫ t, φ.normed volume t • (ℓ i (Φ (y - t)))) x =
      ∫ t, φ.normed volume t • iteratedFDeriv ℝ k (fun x => ℓ i (Φ x)) (x - t) :=
    u3_conv_iter_local (φ.normed volume) φ.continuous_normed
      (by rw [φ.support_normed_eq]; exact Metric.ball_subset_ball hφ) k _
      ((hΦm i).of_le (by exact_mod_cast hk)) x
  have h3 : ‖iteratedFDeriv ℝ k ((ℓ i) ∘ (u3_moll φ Φ)) x‖ ≤ B * nrm i := by
    rw [hcomp, h2]
    have hint : Integrable (φ.normed volume) volume := φ.integrable_normed
    calc ‖∫ t, φ.normed volume t • iteratedFDeriv ℝ k (fun x => ℓ i (Φ x)) (x - t)‖
        ≤ ∫ t, φ.normed volume t * (B * nrm i) :=
          norm_integral_le_of_norm_le (hint.mul_const _) (Eventually.of_forall fun t => by
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
            exact mul_le_mul_of_nonneg_left (hΦb i k hk _) (φ.nonneg_normed t))
      _ = B * nrm i := by rw [integral_mul_const, φ.integral_normed, one_mul]
  have h4 : |ℓ i (iteratedFDeriv ℝ k (u3_moll φ Φ) x v)| ≤
      ‖iteratedFDeriv ℝ k ((ℓ i) ∘ (u3_moll φ Φ)) x‖ * ∏ j, ‖v j‖ := by
    rw [h1]
    have := ((ℓ i).compContinuousMultilinearMap (iteratedFDeriv ℝ k (u3_moll φ Φ) x)).le_opNorm v
    simpa using this
  refine h4.trans ?_
  calc ‖iteratedFDeriv ℝ k ((ℓ i) ∘ (u3_moll φ Φ)) x‖ * ∏ j, ‖v j‖ ≤ (B * nrm i) * ∏ j, ‖v j‖ :=
        mul_le_mul_of_nonneg_right h3 (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = (B * ∏ j, ‖v j‖) * nrm i := by ring

end Moll

end HRS.MS.SuppU3
