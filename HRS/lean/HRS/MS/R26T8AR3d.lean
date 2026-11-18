import HRS.MS.R26T8AR3c

/-!
# S8.2 T8A R3d: nested jets of `Φ(Y,w) = LI(D²f(Y))(w) + S0(D²f(Y))(w)` (the Newton potential of the leading source) of order `≤ 2`
`r26t8a_R3_nest_Phi`: for `0 < |z| ≤ 1`, `q ≤ 2`:
`‖nest p q Φ X z‖ ≤ C ‖D^p (D²f) X‖ (1 + |z|^(-((s-2)+q)) + [q=0][d=4] |log |z||)`.
The `X`-derivatives only hit the coefficient `D²f` (`B ↦ D^q_z (LI_B + S0_B)` is linear); the `z`-derivatives are bounded by the
homogeneity bounds of `LI` (value, gradient, Hessian) and the uniform `C^2` bound of the smooth part `S0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

@[irreducible] def r26t8a_R3_G (nu : ℝ) (chi : Euc d → ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (w : Euc d) : ℝ :=
  s82n_leadingInverse nu B w + r26t8a_p22_S0 nu chi B w

theorem r26t8a_R3_iter_norm_fderiv (f : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ 1 f x‖ = ‖fderiv ℝ f x‖ := by
  have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 0)
  rw [norm_iteratedFDeriv_zero] at h
  exact h.symm

theorem r26t8a_R3_iter_norm_fderiv2 (f : Euc d → ℝ) (x : Euc d) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 1)
  have h2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ f) (x := x) (n := 0)
  rw [norm_iteratedFDeriv_zero] at h2
  rw [← h2] at h1
  exact h1.symm

set_option maxHeartbeats 3200000 in
theorem r26t8a_R3_nest_Phi_core (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X z : Euc d) (hz : z ≠ 0) (p q : ℕ) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ,
      ‖iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B) z‖ ≤ K * ‖B‖) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d =>
          s82n_leadingInverse nu (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2 +
            r26t8a_p22_S0 nu chi (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2) X z‖ ≤
        K * ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ := by
  have hLc : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, ContDiffAt ℝ (q : WithTop ℕ∞) (s82n_leadingInverse nu B) z := fun B =>
    (r26t8a_p22_L_contDiffAt nu B hz).of_le (by exact_mod_cast le_top)
  have hSc : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, ContDiffAt ℝ (q : WithTop ℕ∞) (r26t8a_p22_S0 nu chi B) z := fun B =>
    ((r26t8a_p22_S0_contDiff hd nu hchi B).of_le (by exact_mod_cast le_top)).contDiffAt
  have hGit : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B) z =
      iteratedFDeriv ℝ q (s82n_leadingInverse nu B) z + iteratedFDeriv ℝ q (r26t8a_p22_S0 nu chi B) z := fun B =>
    by unfold r26t8a_R3_G; exact iteratedFDeriv_add_apply (hLc B) (hSc B)
  have hadd : ∀ B1 B2 : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, iteratedFDeriv ℝ q (r26t8a_R3_G nu chi (B1 + B2)) z =
      iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B1) z + iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B2) z := by
    intro B1 B2
    rw [hGit, hGit, hGit]
    have e1 : s82n_leadingInverse nu (B1 + B2) = fun w => s82n_leadingInverse nu B1 w + s82n_leadingInverse nu B2 w :=
      funext fun w => r26t8a_p22_L_add nu B1 B2 w
    have e2 := r26t8a_p22_S0_add hd nu hchi B1 B2
    have a1 : iteratedFDeriv ℝ q (fun w => s82n_leadingInverse nu B1 w + s82n_leadingInverse nu B2 w) z =
        iteratedFDeriv ℝ q (s82n_leadingInverse nu B1) z + iteratedFDeriv ℝ q (s82n_leadingInverse nu B2) z :=
      iteratedFDeriv_add_apply (hLc B1) (hLc B2)
    have a2 : iteratedFDeriv ℝ q (fun w => r26t8a_p22_S0 nu chi B1 w + r26t8a_p22_S0 nu chi B2 w) z =
        iteratedFDeriv ℝ q (r26t8a_p22_S0 nu chi B1) z + iteratedFDeriv ℝ q (r26t8a_p22_S0 nu chi B2) z :=
      iteratedFDeriv_add_apply (hSc B1) (hSc B2)
    rw [e1, e2, a1, a2]
    abel
  have hsmul : ∀ (c : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), iteratedFDeriv ℝ q (r26t8a_R3_G nu chi (c • B)) z = c • iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B) z := by
    intro c B
    rw [hGit, hGit]
    have e1 : s82n_leadingInverse nu (c • B) = fun w => c * s82n_leadingInverse nu B w :=
      funext fun w => r26t8a_p22_L_smul nu c B w
    have e2 := r26t8a_p22_S0_smul nu c hchi B
    have a1 : iteratedFDeriv ℝ q (fun w => c * s82n_leadingInverse nu B w) z =
        c • iteratedFDeriv ℝ q (s82n_leadingInverse nu B) z := iteratedFDeriv_const_smul_apply' (a := c) (hLc B)
    have a2 : iteratedFDeriv ℝ q (fun w => c * r26t8a_p22_S0 nu chi B w) z =
        c • iteratedFDeriv ℝ q (r26t8a_p22_S0 nu chi B) z := iteratedFDeriv_const_smul_apply' (a := c) (hSc B)
    rw [e1, e2, a1, a2, smul_add]
  have hb : ContDiff ℝ (p : WithTop ℕ∞) (fderiv ℝ (fderiv ℝ f)) := by
    have h2 : ContDiff ℝ ((p + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) :=
      (contDiff_infty.1 hf (p + 2)).fderiv_right (m := ((p + 1 : ℕ) : WithTop ℕ∞)) (by exact_mod_cast le_refl (p + 2))
    exact h2.fderiv_right (m := (p : WithTop ℕ∞)) (by exact_mod_cast le_refl (p + 1))
  have hnest := r26t8a_R3_nest_lin (r26t8a_R3_G nu chi) z q K hK0 hadd hsmul hK p
    (fun Y => fderiv ℝ (fderiv ℝ f) Y) hb X
  unfold r26t8a_R3_G at hnest
  exact hnest

theorem r26t8a_R3_G_iter (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {z : Euc d} (hz : z ≠ 0)
    (q : ℕ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B) z =
      iteratedFDeriv ℝ q (s82n_leadingInverse nu B) z + iteratedFDeriv ℝ q (r26t8a_p22_S0 nu chi B) z := by
  have hLc : ContDiffAt ℝ (q : WithTop ℕ∞) (s82n_leadingInverse nu B) z :=
    (r26t8a_p22_L_contDiffAt nu B hz).of_le (by exact_mod_cast le_top)
  have hSc : ContDiffAt ℝ (q : WithTop ℕ∞) (r26t8a_p22_S0 nu chi B) z :=
    ((r26t8a_p22_S0_contDiff hd nu hchi B).of_le (by exact_mod_cast le_top)).contDiffAt
  unfold r26t8a_R3_G
  exact iteratedFDeriv_add_apply hLc hSc

end HRS.MS.R26T8A
