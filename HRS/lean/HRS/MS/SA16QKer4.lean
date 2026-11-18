import HRS.MS.SA16QKer3

/-!
# S.A.16 (SA16Q), E6 part 4: integration by parts against the Riesz kernel

`sa16q_ibp_abstract`: if smooth `kn → k` and `∂_j kn → k'` pointwise off `0`, with integrable majorants
(`sa16q_WI`), then `∫ k ∂_jφ(x - y) dy = ∫ k' φ(x - y) dy` for `C¹` decaying `φ`.

* `sa16q_ibp_g`: `∫ g(y) ∂_jφ(x-y) dy = ∫ ∂_j g(y) φ(x-y) dy`, `0 ≤ s ≤ d-2`;
* `sa16q_ibp_K1`: `∫ K1_i(y) ∂_jφ(x-y) dy = ∫ K2_{ij}(y) φ(x-y) dy`, `0 ≤ s < d-2`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Ibp
variable {d : ℕ}

lemma sa16q_ae_ne (hd : 1 ≤ d) : ∀ᵐ y : Euc d ∂volume, y ≠ 0 :=
  HRS.Commutator.Whole.ae_ne_zero_euc hd

theorem sa16q_ibp_abstract (hd : 1 ≤ d) (j : Fin d) (x : Euc d) {φ : Euc d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hφd : Differentiable ℝ φ) (hφc : Continuous (fderiv ℝ φ))
    (hφ : sa16q_Dec C φ) (hφ' : sa16q_Dec C (fderiv ℝ φ))
    (kn kn' : ℕ → Euc d → ℝ) (k k' m0 m1 : Euc d → ℝ)
    (hkm : ∀ n, Measurable (kn n)) (hkm' : ∀ n, Measurable (kn' n))
    (hk : Measurable k) (hk' : Measurable k')
    (hm0 : Measurable m0) (hm1 : Measurable m1) (hW0 : sa16q_WI m0) (hW1 : sa16q_WI m1)
    (hdiff : ∀ n y, DifferentiableAt ℝ (kn n) y)
    (hfd : ∀ n y, fderiv ℝ (kn n) y (EuclideanSpace.single j (1 : ℝ)) = kn' n y)
    (hb0 : ∀ n y, y ≠ 0 → ‖kn n y‖ ≤ m0 y) (hb1 : ∀ n y, y ≠ 0 → ‖kn' n y‖ ≤ m1 y)
    (hl : ∀ y, y ≠ 0 → Tendsto (fun n => kn n y) atTop (𝓝 (k y)))
    (hl' : ∀ y, y ≠ 0 → Tendsto (fun n => kn' n y) atTop (𝓝 (k' y))) :
    ∫ y, k y * fderiv ℝ φ (x - y) (EuclideanSpace.single j (1 : ℝ)) = ∫ y, k' y * φ (x - y) := by
  set e : Euc d := EuclideanSpace.single j (1 : ℝ) with he
  set ψ' : Euc d → ℝ := fun z => fderiv ℝ φ z e with hψ'
  have hψ'c : Continuous ψ' := hφc.clm_apply continuous_const
  have hψ'D : sa16q_Dec C ψ' := by
    intro z
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have : ‖e‖ = 1 := by simp [he, EuclideanSpace.norm_single]
    rw [this, mul_one]
    exact hφ' z
  have hφc0 : Continuous φ := hφd.continuous
  have hI0 := sa16q_conv_integrable hm0 hW0 hC hφc0 hφ x
  have hI0' := sa16q_conv_integrable hm0 hW0 hC hψ'c hψ'D x
  have hI1 := sa16q_conv_integrable hm1 hW1 hC hφc0 hφ x
  have hne := sa16q_ae_ne (d := d) hd
  -- the derivative of `y ↦ φ (x - y)`
  have hgd : ∀ y, HasFDerivAt (fun y : Euc d => φ (x - y))
      ((fderiv ℝ φ (x - y)).comp (-(ContinuousLinearMap.id ℝ (Euc d)))) y := by
    intro y
    have h1 : HasFDerivAt (fun y : Euc d => x - y) (-(ContinuousLinearMap.id ℝ (Euc d))) y :=
      (hasFDerivAt_id y).const_sub x
    exact (hφd (x - y)).hasFDerivAt.comp y h1
  have hgdv : ∀ y, fderiv ℝ (fun y : Euc d => φ (x - y)) y e = -ψ' (x - y) := by
    intro y
    rw [(hgd y).fderiv]
    simp [hψ']
  have hstep : ∀ n, ∫ y, kn n y * ψ' (x - y) = ∫ y, kn' n y * φ (x - y) := by
    intro n
    have hint0 : Integrable (fun y => kn n y * φ (x - y)) := by
      refine hI0.norm.mono' ((hkm n).aestronglyMeasurable.mul
        (hφc0.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
      filter_upwards [hne] with y hy
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb0 n y hy).trans (Real.le_norm_self _)) (norm_nonneg _)
    have hint1 : Integrable (fun y => kn' n y * φ (x - y)) := by
      refine hI1.norm.mono' ((hkm' n).aestronglyMeasurable.mul
        (hφc0.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
      filter_upwards [hne] with y hy
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb1 n y hy).trans (Real.le_norm_self _)) (norm_nonneg _)
    have hint2 : Integrable (fun y => kn n y * ψ' (x - y)) := by
      refine hI0'.norm.mono' ((hkm n).aestronglyMeasurable.mul
        (hψ'c.comp (continuous_const.sub continuous_id)).aestronglyMeasurable) ?_
      filter_upwards [hne] with y hy
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb0 n y hy).trans (Real.le_norm_self _)) (norm_nonneg _)
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := kn n) (g := fun y : Euc d => φ (x - y)) (v := e)
      (by simpa [hfd] using hint1)
      (by
        simp only [hgdv]
        simpa using hint2.neg)
      hint0 (fun y _ => hdiff n y) (fun y _ => (hgd y).differentiableAt)
    simp only [hgdv, hfd] at hibp
    simp only [mul_neg, integral_neg, neg_inj] at hibp
    exact hibp
  -- limits
  have hlimL : Tendsto (fun n => ∫ y, kn n y * ψ' (x - y)) atTop (𝓝 (∫ y, k y * ψ' (x - y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖m0 y * ψ' (x - y)‖) (fun n => ?_)
      hI0'.norm ?_ ?_
    · exact (hkm n).aestronglyMeasurable.mul (hψ'c.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · intro n
      filter_upwards [hne] with y hy
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb0 n y hy).trans (Real.le_norm_self _)) (norm_nonneg _)
    · filter_upwards [hne] with y hy
      exact (hl y hy).mul_const _
  have hlimR : Tendsto (fun n => ∫ y, kn' n y * φ (x - y)) atTop (𝓝 (∫ y, k' y * φ (x - y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖m1 y * φ (x - y)‖) (fun n => ?_)
      hI1.norm ?_ ?_
    · exact (hkm' n).aestronglyMeasurable.mul (hφc0.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · intro n
      filter_upwards [hne] with y hy
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right ((hb1 n y hy).trans (Real.le_norm_self _)) (norm_nonneg _)
    · filter_upwards [hne] with y hy
      exact (hl' y hy).mul_const _
  have : (fun n => ∫ y, kn n y * ψ' (x - y)) = fun n => ∫ y, kn' n y * φ (x - y) := funext hstep
  rw [this] at hlimL
  exact tendsto_nhds_unique hlimL hlimR

end Ibp

end HRS.Whole.AppendixA.Phase2SA16Q
