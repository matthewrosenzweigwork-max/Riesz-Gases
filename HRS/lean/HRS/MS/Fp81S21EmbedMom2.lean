import HRS.MS.Fp81S21EmbedMom

/-! Compact-test dual norms transfer through the adjoint chart embedding. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_dualNormE_congr_compact
    {d r : ℕ} {Pw : ℝ}
    (T U : (Euc d → ℝ) → ℝ)
    (hTU : ∀ f, IsR2Test f → T f = U f) :
    dualNormE r Pw T = dualNormE r Pw U := by
  unfold dualNormE
  apply iSup_congr
  intro f
  apply iSup_congr
  intro hf
  rw [hTU f ⟨hf.1, hf.2.1⟩]

/-- The target compact-test dual norm of a field equals the norm of its
embedded coefficient vector. The dual norm is identified on the compact
core on which `dualNormE` is defined. -/
theorem fp81s21_embedField_dualNorm_transfer
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (z : r26t6_Coeff) (Q : (Euc d → ℝ) → ℝ)
    (hQ : ∀ f, IsR2Test f → fp81s21_chartAction Es z f = Q f) :
    dualNormE (q + 2) Pw Q =
      ENNReal.ofReal ‖fp81s21_embedField hP hPs Es E z‖ := by
  have hQtarget : ∀ f, IsR2Test f →
      Q f = fp81s21_chartAction E (fp81s21_embedField hP hPs Es E z) f := by
    intro f hf
    calc
      Q f = fp81s21_chartAction Es z f := (hQ f hf).symm
      _ = fp81s21_chartAction E (fp81s21_embedField hP hPs Es E z) f :=
        (fp81s21_embedField_action hP hPs Es E z f hf).symm
  calc
    dualNormE (q + 2) Pw Q =
        dualNormE (q + 2) Pw
          (fp81s21_chartAction E (fp81s21_embedField hP hPs Es E z)) :=
      fp81s21_dualNormE_congr_compact Q
        (fp81s21_chartAction E (fp81s21_embedField hP hPs Es E z)) hQtarget
    _ = ENNReal.ofReal ‖fp81s21_embedField hP hPs Es E z‖ :=
      fp81s21_chartAction_dualNorm hP E (fp81s21_embedField hP hPs Es E z)

#print axioms HRS.Fp81.S21.fp81s21_embedField_dualNorm_transfer

end HRS.Fp81.S21
