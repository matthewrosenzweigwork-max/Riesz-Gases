import HRS.MS.Fp81S21WickB310

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))

/-- The finite-rank map is continuous with the sharp polynomial bound. -/
def fp81s21_wickB311_continuous : fp81s21_wickB32_finiteRankSubmodule μ →L[ℝ] Lp ℝ 2 P :=
  (fp81s21_wickB39_linear L Kstar hL hJoint).mkContinuous
    (Kstar ^ 2 / Real.sqrt 2) (fp81s21_wickB39_linear_bound L Kstar hL hJoint)

theorem fp81s21_wickB311_continuous_norm :
    ‖fp81s21_wickB311_continuous L Kstar hL hJoint‖ ≤ Kstar ^ 2 / Real.sqrt 2 := by
  exact LinearMap.mkContinuous_norm_le _ (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) _

theorem fp81s21_wickB311_extension_eq
    (x : fp81s21_wickB32_finiteRankSubmodule μ) :
    (fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
      (fp81s21_wickB310_inclusion (μ := μ)) (fp81s21_wickB310_inclusion x) =
      fp81s21_wickB39_linear L Kstar hL hJoint x := by
  apply LinearMap.extendOfNorm_eq fp81s21_wickB310_dense
  refine ⟨Kstar ^ 2 / Real.sqrt 2, ?_⟩
  intro y
  exact fp81s21_wickB39_linear_bound L Kstar hL hJoint y

theorem fp81s21_wickB311_operator_apply_bound (k : Lp ℝ 2 (μ.prod μ)) :
    ‖fp81s21_wickG_operator L Kstar hL hJoint k‖ ≤
      Kstar ^ 2 / Real.sqrt 2 * ‖k‖ := by
  have h := LinearMap.norm_extendOfNorm_apply_le
    (f := fp81s21_wickB39_linear L Kstar hL hJoint)
    (e := fp81s21_wickB310_inclusion (μ := μ)) fp81s21_wickB310_dense
    (Kstar ^ 2 / Real.sqrt 2) (fun x => fp81s21_wickB39_linear_bound L Kstar hL hJoint x)
    (fp81s21_wickB310_symmetrize k)
  change ‖fp81s21_wickG_operator L Kstar hL hJoint k‖ ≤
    Kstar ^ 2 / Real.sqrt 2 * ‖fp81s21_wickB23_symmetrize μ k‖ at h
  exact h.trans (mul_le_mul_of_nonneg_left (fp81s21_wickB23_symmetrize_contracting μ k)
    (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)))

theorem fp81s21_wickB311_operator_norm :
    ‖fp81s21_wickG_operator L Kstar hL hJoint‖ ≤ Kstar ^ 2 / Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  exact fp81s21_wickB311_operator_apply_bound L Kstar hL hJoint

theorem fp81s21_wickB311_operator_symmetrize (k : Lp ℝ 2 (μ.prod μ)) :
    fp81s21_wickG_operator L Kstar hL hJoint k =
      fp81s21_wickG_operator L Kstar hL hJoint (fp81s21_wickB23_symmetrize μ k) := by
  change (fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB310_inclusion (μ := μ)) (fp81s21_wickB310_symmetrize k) =
      (fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
        (fp81s21_wickB310_inclusion (μ := μ))
        (fp81s21_wickB310_symmetrize (fp81s21_wickB23_symmetrize μ k))
  congr 1
  apply Subtype.ext
  exact (fp81s21_wickB23_symmetrize_idempotent μ k).symm

theorem fp81s21_wickB311_operator_finite
    (x : fp81s21_wickB32_finiteRankSubmodule μ) :
    fp81s21_wickG_operator L Kstar hL hJoint x =
      fp81s21_wickB39_linear L Kstar hL hJoint x := by
  have hfixed := fp81s21_wickB32_finiteRank_le_symmetric μ x.property
  change fp81s21_wickB23_symmetrize μ x - x = 0 at hfixed
  have hsym : fp81s21_wickB310_symmetrize x = fp81s21_wickB310_inclusion x := by
    apply Subtype.ext
    exact sub_eq_zero.mp hfixed
  change (fp81s21_wickB39_linear L Kstar hL hJoint).extendOfNorm
    (fp81s21_wickB310_inclusion (μ := μ)) (fp81s21_wickB310_symmetrize x) = _
  rw [hsym, fp81s21_wickB311_extension_eq]

#print axioms fp81s21_wickB311_continuous_norm
#print axioms fp81s21_wickB311_extension_eq
#print axioms fp81s21_wickB311_operator_apply_bound
#print axioms fp81s21_wickB311_operator_norm
#print axioms fp81s21_wickB311_operator_symmetrize
#print axioms fp81s21_wickB311_operator_finite

end HRS.Fp81.S21
end
