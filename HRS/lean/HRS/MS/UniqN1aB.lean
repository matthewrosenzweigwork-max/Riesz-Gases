import HRS.MS.UniqN1aA
import HRS.MH.ScreenedL1Aux1

/-!
# N1a of `UniqPlan.md`, part (b): integration by parts against a kernel with an integrable singularity

For `k` of class `C¹` off the origin, locally integrable together with `∂_jk`, and `|k(z)| ≤ A‖z‖^{-a}`
near `0` with `0 ≤ a`, `a + 1 < d`, and `F ∈ C¹_c`:
`∫ k(y-x) ∂_jF(x) dx = ∫ (∂_jk)(y-x) F(x) dx` (`n1a_weak_deriv`).
Proof: integrate by parts against `F · Φ_ε(y-·)` with the cutoff `Φ_ε` of part (a) and let `ε → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1a

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0

variable {d : ℕ}

theorem n1a_conv_integrable {k : Euc d → ℝ} (hk : LocallyIntegrable k volume) {h : Euc d → ℝ}
    (hh : Continuous h) (hhc : HasCompactSupport h) (y : Euc d) :
    Integrable (fun x => k (y - x) * h x) volume := by
  have := hhc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hh hk y
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [mul_comm]

/-- Integration by parts with the cutoff `Φ_ε(y - ·)`. -/
theorem n1a_ibp_eps {k : Euc d → ℝ} (j : Fin d) (hkd : ∀ z, z ≠ 0 → ContDiffAt ℝ 1 k z)
    {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (y : Euc d) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x, k (y - x) * (F x * fderiv ℝ (fun x => n1aΦ ε (y - x)) x (EuclideanSpace.single j 1) +
        n1aΦ ε (y - x) * fderiv ℝ F x (EuclideanSpace.single j 1)) =
      ∫ x, fderiv ℝ k (y - x) (EuclideanSpace.single j 1) * (F x * n1aΦ ε (y - x)) := by
  set Φ : Euc d → ℝ := fun x => n1aΦ ε (y - x) with hΦdef
  have hΦ : ContDiff ℝ 1 Φ :=
    ((n1aΦ_contDiff (d := d) ε).of_le (by exact_mod_cast le_top)).comp
      (contDiff_const.sub contDiff_id)
  have hG : ContDiff ℝ 1 (fun x => F x * Φ x) := hF.mul hΦ
  have hGc : HasCompactSupport (fun x => F x * Φ x) := hFc.mul_right
  have hsupp : tsupport (fun x => F x * Φ x) ⊆ {t | ε ≤ ‖y - t‖} := by
    refine closure_minimal (fun t ht => ?_) (isClosed_le continuous_const
      (continuous_norm.comp (continuous_const.sub continuous_id)))
    by_contra h
    have h' : ‖y - t‖ < ε := not_le.1 h
    apply ht
    simp only [hΦdef]
    rw [n1aΦ_zero hε h'.le, mul_zero]
  have hne : ∀ t ∈ tsupport (fun x => F x * Φ x), y - t ≠ 0 := by
    intro t ht h0
    have := hsupp ht
    simp only [Set.mem_ofPred_eq, h0, norm_zero] at this
    linarith
  have hk : ∀ t ∈ tsupport (fun x => F x * Φ x), ContDiffAt ℝ 1 (fun x => k (y - x)) t :=
    fun t ht => (hkd _ (hne t ht)).comp t (contDiffAt_const.sub contDiffAt_id)
  have key := n0_ibp hG hGc hk (EuclideanSpace.single j (1 : ℝ))
  rw [← integral_neg] at key
  convert key using 1
  · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    congr 1
    rw [fderiv_fun_mul (hF.differentiable one_ne_zero t) (hΦ.differentiable one_ne_zero t)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    by_cases h0 : y - t = 0
    · have : n1aΦ ε (y - t) = 0 := by rw [h0]; exact n1aΦ_zero hε (by simp [hε.le])
      simp [hΦdef, this]
    · have hd : HasFDerivAt (fun x => k (y - x))
          ((fderiv ℝ k (y - t)).comp (0 - ContinuousLinearMap.id ℝ (Euc d))) t :=
        ((hkd _ h0).differentiableAt one_ne_zero).hasFDerivAt.comp t
          ((hasFDerivAt_const y t).sub (hasFDerivAt_id t))
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.comp_apply, zero_sub, neg_apply,
        ContinuousLinearMap.id_apply, map_neg]
      ring

end HRS.MS.UniqN1a
