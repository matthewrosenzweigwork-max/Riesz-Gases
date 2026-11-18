import HRS.MS.Fp81S21InitialCancel3

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
open S45

/-- The actual-law pair-kernel integrability contract from the density envelope. -/
theorem fp81s21_initialCancel_wr8
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {B : ℝ} {h : Euc p.d → Euc p.d → ℝ}
    (hh : IsBoundedPairKernel p.s B h) :
    HRS.MS.Wr.Wr8Ok (r26t3_mu R 0) h := by
  have hd : 2 ≤ p.d := p.hd
  have hd1 : 1 ≤ p.d := by omega
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith [p.hs]
  have hM : ∀ x, R.ρ 0 x ≤ E.C := by
    intro x
    have h0 := E.reference.h0 x
    have hE : Real.exp (-E.c * ‖x‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by
        have hc := E.reference.hc
        have hnorm := sq_nonneg ‖x‖
        nlinarith)
    have hC := E.reference.C0
    calc R.ρ 0 x ≤ |R.ρ 0 x| := le_abs_self _
      _ ≤ E.C * Real.exp (-E.c * ‖x‖ ^ 2) := h0
      _ ≤ E.C := mul_le_of_le_one_right hC hE
  obtain ⟨hrow, hprod, -⟩ := HRS.MS.R2Mt.s92_kernel_integrable
    hd1 p.hs0 hsd E.C E.reference.prob hM hh
  have hrows : ∀ x, Integrable (h x) (r26t3_mu R 0) := by
    intro x
    simpa [r26t3_mu] using hrow x
  have hp : Integrable (Function.uncurry h)
      ((r26t3_mu R 0).prod (r26t3_mu R 0)) := by
    simpa [r26t3_mu] using hprod
  exact ⟨hh.measurable, hrows, hp⟩

/-- The differentiated initial-law convolution is linear in arbitrary directions. -/
theorem fp81s21_initialCancel_Gpot_fderiv_gen
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {u : Euc p.d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ}
    (hBu : ∀ x, |u x| ≤ Bu) (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du)
    (hdiff : Differentiable ℝ (fp81s21_initialCancel_Gpot R u))
    (x e : Euc p.d) :
    fderiv ℝ (fp81s21_initialCancel_Gpot R u) x e =
      ∫ y, rieszKernel p.d p.s (x - y) *
        fderiv ℝ (fp81s21_initialCancel_rr R u) y e := by
  set t : ℝ := 1 + ‖e‖ with ht
  have ht0 : 0 < t := by have := norm_nonneg e; positivity
  set e' : Euc p.d := t⁻¹ • e with he'
  have he'1 : ‖e'‖ ≤ 1 := by
    rw [he', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]
    rw [inv_mul_le_iff₀ ht0]
    simp only [ht]
    linarith
  have h1 := fp81s21_initialCancel_Gpot_fderiv R E hu hBu hDu hdiff x e' he'1
  have heq : e = t • e' := by
    rw [he', smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
  have hder : fderiv ℝ (fp81s21_initialCancel_Gpot R u) x e =
      t * fderiv ℝ (fp81s21_initialCancel_Gpot R u) x e' := by
    conv_lhs => rw [heq]
    rw [map_smul, smul_eq_mul]
  have hder' : ∀ y, fderiv ℝ (fp81s21_initialCancel_rr R u) y e =
      t * fderiv ℝ (fp81s21_initialCancel_rr R u) y e' := by
    intro y
    conv_lhs => rw [heq]
    rw [map_smul, smul_eq_mul]
  rw [hder, h1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  calc t * (rieszKernel p.d p.s (x - y) *
        fderiv ℝ (fp81s21_initialCancel_rr R u) y e') =
      rieszKernel p.d p.s (x - y) *
        (t * fderiv ℝ (fp81s21_initialCancel_rr R u) y e') := by ring
    _ = rieszKernel p.d p.s (x - y) *
        fderiv ℝ (fp81s21_initialCancel_rr R u) y e := by rw [← hder' y]

/-- The actual-law row formula: commutator convolution equals the potential
derivative minus the convolution of the weighted divergence. -/
theorem fp81s21_initialCancel_row
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {u : Euc p.d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ}
    (hBu : ∀ x, |u x| ≤ Bu) (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du)
    (hdiff : Differentiable ℝ (fp81s21_initialCancel_Gpot R u))
    {χ : Euc p.d → ℝ} (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (x : Euc p.d) :
    ∫ y, fp81s21_initialCancel_rr R u y *
      commutatorKernel p.d p.s (gradient χ) x y =
      fderiv ℝ (fp81s21_initialCancel_Gpot R u) x (gradient χ x) -
        ∫ y, rieszKernel p.d p.s (x - y) *
          fp81s21_initialCancel_Dd R u (gradient χ) y := by
  have hd : 2 ≤ p.d := p.hd
  have hd1 : 1 ≤ p.d := by omega
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith [p.hs]
  obtain ⟨hr1, hr0, hr1'⟩ := fp81s21_initialCancel_r_bounds R E hu hBu hDu
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hC' : 0 ≤ E.C * (Bu + Du + 1) := by
    have hC := E.reference.C0
    positivity
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
  have hobi := s45_obi hd1 p.hs0 hsd E.reference.hc hC' hr1 hr0 hr1' hv1 hB1 hB2 x
  have hcomm : ∀ y, commutatorKernel p.d p.s (gradient χ) x y =
      ⟪gradient χ x - gradient χ y, rieszKernelGrad p.d p.s (x - y)⟫ := fun y => rfl
  simp_rw [hcomm]
  have hobi' :
      (∫ y, fp81s21_initialCancel_rr R u y *
        ⟪gradient χ x - gradient χ y, rieszKernelGrad p.d p.s (x - y)⟫) =
      ∫ y, rieszKernel p.d p.s (x - y) *
        (⟪gradient (fp81s21_initialCancel_rr R u) y,
            gradient χ x - gradient χ y⟫ -
          fp81s21_initialCancel_rr R u y * s45_div (gradient χ) y) := hobi
  rw [hobi']
  have hpt : ∀ y, rieszKernel p.d p.s (x - y) *
      (⟪gradient (fp81s21_initialCancel_rr R u) y,
        gradient χ x - gradient χ y⟫ -
        fp81s21_initialCancel_rr R u y * s45_div (gradient χ) y) =
      rieszKernel p.d p.s (x - y) *
        fderiv ℝ (fp81s21_initialCancel_rr R u) y (gradient χ x) -
      rieszKernel p.d p.s (x - y) *
        fp81s21_initialCancel_Dd R u (gradient χ) y := by
    intro y
    unfold fp81s21_initialCancel_Dd
    have hin : ⟪gradient (fp81s21_initialCancel_rr R u) y, gradient χ x⟫ =
        fderiv ℝ (fp81s21_initialCancel_rr R u) y (gradient χ x) := by
      rw [real_inner_comm]
      exact HRS.MS.PoisKolm.kl_inner_gradient
        (fp81s21_initialCancel_rr R u) y (gradient χ x)
    rw [inner_sub_right, hin]
    ring
  simp_rw [hpt]
  have hrc : Continuous (fderiv ℝ (fp81s21_initialCancel_rr R u)) :=
    hr1.continuous_fderiv one_ne_zero
  have hexp := fun y : Euc p.d => (Real.exp_pos (-E.c * ‖y‖ ^ 2)).le
  have I1 : Integrable (fun y => rieszKernel p.d p.s (x - y) *
      fderiv ℝ (fp81s21_initialCancel_rr R u) y (gradient χ x)) := by
    refine fp81s21_initialCancel_LI_g R E
      ((hrc.clm_apply continuous_const)) (K := E.C * (Bu + Du + 1) * B1)
      (by positivity) (fun y => ?_) x
    calc |fderiv ℝ (fp81s21_initialCancel_rr R u) y (gradient χ x)| ≤
          ‖fderiv ℝ (fp81s21_initialCancel_rr R u) y‖ * ‖gradient χ x‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) * B1 :=
            mul_le_mul (hr1' y) (hB1 x) (norm_nonneg _) (by positivity)
      _ = E.C * (Bu + Du + 1) * B1 * Real.exp (-E.c * ‖y‖ ^ 2) := by ring
  have hDc : Continuous (fp81s21_initialCancel_Dd R u (gradient χ)) :=
    (fp81s21_initialCancel_Dd_bd R E hu hBu hDu hv1 hB1 hB2).1
  have hDb : ∀ y, |fp81s21_initialCancel_Dd R u (gradient χ) y| ≤
      E.C * (Bu + Du + 1) * (B1 + p.d * B2) * Real.exp (-E.c * ‖y‖ ^ 2) :=
    (fp81s21_initialCancel_Dd_bd R E hu hBu hDu hv1 hB1 hB2).2
  have I2 : Integrable (fun y => rieszKernel p.d p.s (x - y) *
      fp81s21_initialCancel_Dd R u (gradient χ) y) := by
    refine fp81s21_initialCancel_LI_g R E hDc
      (K := E.C * (Bu + Du + 1) * (B1 + p.d * B2)) (by positivity)
      (fun y => hDb y) x
  rw [integral_sub I1 I2]
  have hgen := fp81s21_initialCancel_Gpot_fderiv_gen R E hu hBu hDu hdiff
    x (gradient χ x)
  rw [hgen]

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initialCancel_wr8
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_Gpot_fderiv_gen
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_row
