import HRS.MS.Fp81S21JointG4

/-! The joint spatial projection tail for the fixed Gaussian selectors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The physical Gaussian pair has the sum of its two spatial tails. -/
theorem fp81s21_jointG_projection_tail
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εG εB : ℕ → ℝ) (S : fp81s21_GaussianPhysical31 p R Es E εG εB)
    (G : GaussianRealization R) (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (Vη VB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hVη : fp81s21_TimeL2Rep G.P
      (fp81s21_gaussian_embedFamily p Es E (S.qsηG G)) S.MηG a H Vη)
    (hVB : fp81s21_TimeL2Rep G.P (S.quadratic.qe G)
      (S.quadratic.Kstar ^ 4 * S.quadratic.B / 2) a H VB)
    (m : ℕ) (hεG : 0 ≤ εG m) (hεB : 0 ≤ εB m) :
    fp81s21_SqErr G.P (fun ω => (Vη ω, VB ω))
      (fun ω => (fp81s21_timeProject H m (Vη ω), fp81s21_timeProject H m (VB ω)))
      (Real.sqrt (H * S.MηG) * εG m +
        Real.sqrt (H * (S.quadratic.Kstar ^ 4 * S.quadratic.B / 2)) * εB m) := by
  exact fp81s21_jointG_pair_sqerr G.P Vη (fun ω => fp81s21_timeProject H m (Vη ω))
    VB (fun ω => fp81s21_timeProject H m (VB ω)) _ _
    (mul_nonneg (Real.sqrt_nonneg _) hεG) (mul_nonneg (Real.sqrt_nonneg _) hεB)
    (fp81s21_jointG_linear_projection_tail p R Es E εG εB S G a H ha hH Vη hVη m)
    (fp81s21_jointG_quadratic_projection_tail p R Es E εG εB S G a H ha hH VB hVB m)

#print axioms fp81s21_jointG_projection_tail
end HRS.Fp81.S21
end
