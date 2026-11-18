import HRS.MS.Fp81S21InitialCancel

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc cbNorm MemCb)
open HRS.Whole
open HRS.MS.R26T3

/-- The actual-law cubic coefficient `∫ w_{jk} a_m dμ⁰`. -/
def fp81s21_initialCancel_cc {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) {φ : ℕ → Euc p.d → ℝ}
    (F : InitialFamData R φ) (j k m : ℕ) : ℝ :=
  ∫ x, InitialFamData.wF F j k x * r26t3_a R (φ m) x ∂(r26t3_mu R 0)

/-- The actual-law commutator coefficient `∬ h a_k a_m dμ⁰ dμ⁰`. -/
def fp81s21_initialCancel_Qk {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (φ : ℕ → Euc p.d → ℝ)
    (h : Euc p.d → Euc p.d → ℝ) (k m : ℕ) : ℝ :=
  ∫ z : Euc p.d × Euc p.d,
    h z.1 z.2 * r26t3_a R (φ k) z.1 * r26t3_a R (φ m) z.2
      ∂((r26t3_mu R 0).prod (r26t3_mu R 0))

/-- The actual-law spatial integration by parts supplied by S47. -/
theorem fp81s21_initialCancel_ibp_mu
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (j : ℕ)
    {ψ : Euc p.d → ℝ} (hψ : ContDiff ℝ 1 ψ) {Bψ Dψ : ℝ}
    (hBψ : ∀ x, |ψ x| ≤ Bψ)
    (hDψ : ∀ x, ‖fderiv ℝ ψ x‖ ≤ Dψ) :
    ∫ y, ψ y * weightedGen (R.ρ 0) (F.χ j) y ∂(r26t3_mu R 0) =
      ∫ y, ⟪gradient ψ y, gradient (F.χ j) y⟫ ∂(r26t3_mu R 0) := by
  have hd : 2 ≤ p.d := p.hd
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by omega))
  have hB1 : ∀ x, ‖gradient (F.χ j) x‖ ≤ F.K * cbNorm (fp81s21_J1 p.d) (φ j) := by
    intro x
    rw [S45.s45_norm_gradient, ← norm_iteratedFDeriv_one]
    exact F.deriv j x 0 (Nat.zero_le _)
  have hB2 : ∀ x, ‖fderiv ℝ (gradient (F.χ j)) x‖ ≤
      F.K * cbNorm (fp81s21_J1 p.d) (φ j) := by
    intro x
    exact (S45.s45_norm_fderiv_gradient hχ2 x).trans
      (F.deriv j x 1 (by have hk := fp81s21_k0_ge_one p.d; omega))
  simpa only [r26t3_mu] using
    (S47.s47_ibp_mu E.reference hχ2 hB1 hB2 hψ hBψ hDψ)

/-- With `∇χ_j` in the S9.9 normalization, weighted IBP gives the cubic
generator pairing with its exact factor `γ`. -/
theorem fp81s21_initialCancel_ibp_gen
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (j : ℕ)
    {ψ : Euc p.d → ℝ} (hψ : ContDiff ℝ 1 ψ) {Bψ Dψ : ℝ}
    (hBψ : ∀ x, |ψ x| ≤ Bψ)
    (hDψ : ∀ x, ‖fderiv ℝ ψ x‖ ≤ Dψ) :
    ∫ y, ψ y * (p.γ * r26t3_a R (φ j) y) ∂(r26t3_mu R 0) =
      ∫ y, ⟪gradient ψ y, gradient (F.χ j) y⟫ ∂(r26t3_mu R 0) := by
  have h := fp81s21_initialCancel_ibp_mu R E F j hψ hBψ hDψ
  have hleft : ∫ y, ψ y * (p.γ * r26t3_a R (φ j) y) ∂(r26t3_mu R 0) =
      ∫ y, ψ y * weightedGen (R.ρ 0) (F.χ j) y ∂(r26t3_mu R 0) := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← F.gen j y]
  exact hleft.trans h

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initialCancel_ibp_mu
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_ibp_gen
