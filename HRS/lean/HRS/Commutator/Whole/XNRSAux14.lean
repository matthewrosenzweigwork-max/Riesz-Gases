import HRS.Commutator.Whole.XNRSAux13

/-!
# Packet X-NRS, part 14: the base case `α' = 0` and the combined bound for `J_m`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- multiplication by `v_c`. -/
def xvmul (v : Euc d → Euc d) (c : Fin d) (h : 𝓢(Euc d, ℂ)) : 𝓢(Euc d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x => v x c) h

lemma xvmul_apply {v : Euc d → Euc d} (hv : XTVF v) (c : Fin d) (h : 𝓢(Euc d, ℂ)) (x : Euc d) :
    xvmul v c h x = ((v x c : ℝ) : ℂ) * h x := by
  unfold xvmul
  rw [SchwartzMap.smulLeftCLM_apply_apply (hv c)]
  simp [Complex.real_smul]

lemma xdr_xvmul {v : Euc d → Euc d} (hv : XTVF v) (a c : Fin d) (h : 𝓢(Euc d, ℂ)) :
    xdr a (xvmul v c h) = xwmul v a c h + xvmul v c (xdr a h) := by
  ext x
  rw [xdr_apply]
  have hfun : (xvmul v c h : Euc d → ℂ) = fun y => ((v y c : ℝ) : ℂ) * h y :=
    funext (xvmul_apply hv c h)
  rw [hfun]
  have h1 : HasFDerivAt (fun y => ((v y c : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (fun y => v y c) x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (((hv c).1.differentiable (by simp)) x).hasFDerivAt
  have h2 : HasFDerivAt (fun y => h y) (fderiv ℝ h x) x := h.differentiableAt.hasFDerivAt
  have h3 : HasLineDerivAt ℝ (fun y => ((v y c : ℝ) : ℂ) * h y)
      (((((v x c : ℝ) : ℂ) • fderiv ℝ h x + h x • Complex.ofRealCLM.comp (fderiv ℝ (fun y => v y c) x))) (xe a))
      x (xe a) := (h1.mul h2).hasLineDerivAt (xe a)
  rw [h3.lineDeriv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  rw [xwmul_apply hv, xvmul_apply hv, xdr_apply,
    h.differentiableAt.lineDeriv_eq_fderiv, ← xw_eq_fderiv v a c hv x]
  ring

lemma xlam_zero {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) :
    xlam 0 ρ h = h := by
  refine xschwartz_ext_fourier fun ξ => ?_
  rw [fourier_xlam_of_inD hρ hh]
  simp

/-- the case `α' = 0`. -/
theorem xbase_zero {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {v : Euc d → Euc d} (hv : XTVF v) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : XLip v L) {h : 𝓢(Euc d, ℂ)} (hh : XInD ρ h) :
    ‖xJ v ρ (2 * 0) h‖ ≤ ((d : ℝ) / 2 * L) * xhom 0 h := by
  have hJ : xJ v ρ (2 * 0) h = ∑ c, ∫ x, h x * (((v x c : ℝ) : ℂ) * xdr c h x) := by
    unfold xJ
    rw [mul_zero, xlam_zero hρ hh]
    have : ∀ x, h x * xadv v h x = ∑ c, h x * (((v x c : ℝ) : ℂ) * xdr c h x) := by
      intro x; rw [xadv_apply hv, Finset.mul_sum]
    simp_rw [this]
    rw [integral_finsetSum _ fun c _ => ?_]
    have := xint_mul h (xvmul v c (xdr c h))
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [xvmul_apply hv]
  have hT : ∀ c : Fin d, ∫ x, h x * (((v x c : ℝ) : ℂ) * xdr c h x) =
      -(1 / 2 : ℂ) * ∫ x, ((xw v c c x : ℝ) : ℂ) * (h x * h x) := by
    intro c
    have hibp := SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left (μ := (volume : Measure (Euc d)))
      (xvmul v c h) h (xe c)
    have e1 : ∫ x, xvmul v c h x * ∂_{xe c} h x = ∫ x, h x * (((v x c : ℝ) : ℂ) * xdr c h x) := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [xvmul_apply hv]
      show ((v x c : ℝ) : ℂ) * h x * xdr c h x = _
      ring
    have e2 : ∫ x, ∂_{xe c} (xvmul v c h) x * h x =
        (∫ x, ((xw v c c x : ℝ) : ℂ) * (h x * h x)) + ∫ x, h x * (((v x c : ℝ) : ℂ) * xdr c h x) := by
      have : ∀ x, (∂_{xe c} (xvmul v c h)) x * h x =
          ((xw v c c x : ℝ) : ℂ) * (h x * h x) + h x * (((v x c : ℝ) : ℂ) * xdr c h x) := by
        intro x
        have := xdr_xvmul hv c c h
        have h5 : (∂_{xe c} (xvmul v c h)) x = xdr c (xvmul v c h) x := rfl
        rw [h5, this, SchwartzMap.add_apply, xwmul_apply hv, xvmul_apply hv]; ring
      have hi1 : Integrable (fun x => ((xw v c c x : ℝ) : ℂ) * (h x * h x)) := by
        have := xint_mul (xwmul v c c h) h
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [xwmul_apply hv]; ring
      have hi2 : Integrable (fun x => h x * (((v x c : ℝ) : ℂ) * xdr c h x)) := by
        have := xint_mul h (xvmul v c (xdr c h))
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [xvmul_apply hv]
      simp_rw [this]
      exact integral_add hi1 hi2
    rw [e1, e2] at hibp
    linear_combination (1 / 2 : ℂ) * hibp
  rw [hJ]
  simp_rw [hT]
  rw [← Finset.mul_sum, norm_mul]
  have h1 : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [h1]
  have hx : xhom 0 h = ∫ x, ‖h x‖ ^ 2 := by
    unfold xhom
    simp only [mul_zero, Real.rpow_zero, one_mul]
    exact SchwartzMap.integral_norm_sq_fourier h
  have hn : ‖∑ c : Fin d, ∫ x, ((xw v c c x : ℝ) : ℂ) * (h x * h x)‖ ≤ (d : ℝ) * L * ∫ x, ‖h x‖ ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ c : Fin d, ‖∫ x, ((xw v c c x : ℝ) : ℂ) * (h x * h x)‖ ≤ L * ∫ x, ‖h x‖ ^ 2 := by
      intro c
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
        ((xint_sq_bdd h).const_mul L) (Eventually.of_forall fun x => ?_)
      show ‖((xw v c c x : ℝ) : ℂ) * (h x * h x)‖ ≤ L * ‖h x‖ ^ 2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_mul, ← sq]
      exact mul_le_mul_of_nonneg_right (xw_le hv hL0 hL c c x) (by positivity)
    calc ∑ c : Fin d, ‖∫ x, ((xw v c c x : ℝ) : ℂ) * (h x * h x)‖ ≤ ∑ c : Fin d, L * ∫ x, ‖h x‖ ^ 2 :=
          Finset.sum_le_sum fun c _ => this c
      _ = (d : ℝ) * L * ∫ x, ‖h x‖ ^ 2 := by simp; ring
  rw [hx]
  nlinarith [hn]


/-- The bound for `J(2α'+2m, h)`, `α' ∈ [0,1)`, from the super-Coulombic estimate and the multiplier
bound. -/
theorem xJbound (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : XGoodCut ρ) {v : Euc d → Euc d} (hv : XTVF v)
    {L K : ℝ} (hL0 : 0 ≤ L) (hLK : L ≤ K) (hL : XLip v L) {α' CB : ℝ} (hα'0 : 0 ≤ α')
    (hα'1 : α' < 1) (hCB : 0 ≤ CB)
    (k : ℕ)
    (hmul : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ (a c : Fin d) (Γ : 𝓢(Euc d, ℂ)), XInD ρ Γ →
      xhom (α' + m - 1) (xwmul v a c Γ) ≤ (CB * K) ^ 2 * xhom (α' + m - 1) Γ) :
    ∀ h : 𝓢(Euc d, ℂ), XInD ρ h →
      ‖xJ v ρ (2 * α' + 2 * k) h‖ ≤
        xC d (((d : ℝ) + ((d : ℝ) + 2 * α' + 2) / 2)) CB k * K * xhom (α' + k) h := by
  have hK : 0 ≤ K := hL0.trans hLK
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set C0 : ℝ := (d : ℝ) + ((d : ℝ) + 2 * α' + 2) / 2 with hC0
  have hC00 : 0 ≤ C0 := by rw [hC0]; positivity
  refine xind hρ hv hK hC00 hCB hα'0 ?_ hmul k le_rfl
  intro h hh
  rcases hα'0.eq_or_lt with h0 | h0
  · subst h0
    refine (xbase_zero hρ hv hL0 hL hh).trans ?_
    have : (d : ℝ) / 2 * L ≤ C0 * K := by
      rw [hC0]
      have : (d : ℝ) / 2 * L ≤ ((d : ℝ) + ((d : ℝ) + 2 * 0 + 2) / 2) * L := by
        apply mul_le_mul_of_nonneg_right _ hL0; linarith
      exact this.trans (mul_le_mul_of_nonneg_left hLK (by positivity))
    exact mul_le_mul_of_nonneg_right this (by
      unfold xhom; exact integral_nonneg fun ξ => by positivity)
  · rw [xJ, integral_xlam_mul hρ hh]
    refine (xsc hd h0 hα'1 hv hL0 hL h).trans ?_
    have hx : 0 ≤ xhom α' h := by unfold xhom; exact integral_nonneg fun ξ => by positivity
    calc ((d : ℝ) + ((d : ℝ) + 2 * α' + 2) / 2) * L * xhom α' h ≤ C0 * K * xhom α' h := by
          rw [← hC0]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLK hC00) hx
      _ = _ := rfl

end HRS.Commutator.Whole.XNRS
