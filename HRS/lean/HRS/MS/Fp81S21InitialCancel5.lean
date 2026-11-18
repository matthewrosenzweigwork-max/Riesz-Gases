import HRS.MS.Fp81S21InitialCancel4

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

/-- The actual-initial-law cubic cancellation identity.  The response, both
coefficients, and the product integral all use `r26t3_mu R 0`. -/
theorem fp81s21_initialCancel_cancel
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ) (j k m : ℕ) :
    fp81s21_initialCancel_cc R F j k m +
        fp81s21_initialCancel_cc R F j m k -
        fp81s21_initialCancel_Qk R φ
          (commutatorKernel p.d p.s (gradient (F.χ j))) k m =
      ∫ x, r26t3_a R (φ j) x * r26t3_a R (φ k) x * r26t3_a R (φ m) x
        ∂(r26t3_mu R 0) := by
  have hsd : p.s < p.d := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  let μ := r26t3_mu R 0
  letI hμ : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  have hφmem : ∀ i, MemCb (fp81s21_J1 p.d) (φ i) := hφ.1
  have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
    have hk := fp81s21_k0_ge_one p.d
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by omega))
  set χ := F.χ j with hχ
  set Bχ : ℝ := F.K * cbNorm (fp81s21_J1 p.d) (φ j)
  have hB1 : ∀ x, ‖gradient χ x‖ ≤ Bχ := by
    intro x
    rw [hχ, S45.s45_norm_gradient, ← norm_iteratedFDeriv_one]
    exact F.deriv j x 0 (Nat.zero_le _)
  have hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ Bχ := by
    intro x
    rw [hχ]
    exact (S45.s45_norm_fderiv_gradient hχ2 x).trans
      (F.deriv j x 1 (by have hk := fp81s21_k0_ge_one p.d; omega))
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hB1 0)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ2
  have hvd : Differentiable ℝ (gradient χ) := hv1.differentiable one_ne_zero
  let Λ : ℝ≥0 := ⟨Bχ, hBχ0⟩
  have hLip : LipschitzWith Λ (gradient χ) :=
    lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
      have hx := hB2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hker : IsBoundedPairKernel p.s ((p.s + 1) * Bχ)
      (commutatorKernel p.d p.s (gradient χ)) := by
    have h := S99.s99_comm_isBounded (d := p.d) p.hs0 Λ hLip
    have hΛ : (Λ : ℝ) = Bχ := rfl
    change IsBoundedPairKernel p.s ((p.s + 1) * (Λ : ℝ))
      (commutatorKernel p.d p.s (gradient χ)) at h
    rw [hΛ] at h
    exact h
  have hwr8 := fp81s21_initialCancel_wr8 R E hker
  have huk := fp81s21_initialCancel_ua hδ hδh R E hγ hφmem F k
  have hum := fp81s21_initialCancel_ua hδ hδh R E hγ hφmem F m
  rcases huk with ⟨huk1, hukb, hukd, hGk1, ⟨MGk, hGkb⟩,
    ⟨DGk, hGkd⟩, hGkfd⟩
  rcases hum with ⟨hum1, humb, humd, hGm1, ⟨MGm, hGmb⟩,
    ⟨DGm, hGmd⟩, hGmfd⟩
  set uk := r26t3_a R (φ k)
  set um := r26t3_a R (φ m)
  set Bk : ℝ := F.K * cbNorm (fp81s21_J1 p.d) (φ k)
  set Bm : ℝ := F.K * cbNorm (fp81s21_J1 p.d) (φ m)
  have hBk0 : 0 ≤ Bk := (abs_nonneg _).trans (hukb 0)
  have hBm0 : 0 ≤ Bm := (abs_nonneg _).trans (humb 0)
  have hDGk0 : 0 ≤ DGk := (norm_nonneg _).trans (hGkd 0)
  have hDGm0 : 0 ≤ DGm := (norm_nonneg _).trans (hGmd 0)
  have hMGk0 : 0 ≤ MGk := (abs_nonneg _).trans (hGkb 0)
  have hMGm0 : 0 ≤ MGm := (abs_nonneg _).trans (hGmb 0)
  have hBχ1 : 0 ≤ Bχ := hBχ0
  let h := commutatorKernel p.d p.s (gradient χ)
  have hwc : Continuous (fun z : Euc p.d × Euc p.d => uk z.1 * um z.2) :=
    (huk1.continuous.comp continuous_fst).mul (hum1.continuous.comp continuous_snd)
  have hint : Integrable (fun z : Euc p.d × Euc p.d => h z.1 z.2 * uk z.1 * um z.2)
      (μ.prod μ) := by
    have hb := hwr8.prod.bdd_mul (f := fun z : Euc p.d × Euc p.d => uk z.1 * um z.2)
      (c := Bk * Bm) hwc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hukb _) (humb _) (abs_nonneg _) hBk0)
    refine hb.congr (Filter.Eventually.of_forall fun z => ?_)
    show uk z.1 * um z.2 * h z.1 z.2 = h z.1 z.2 * uk z.1 * um z.2
    ring
  have hQ1 : fp81s21_initialCancel_Qk R φ h k m =
      ∫ x, ∫ y, h x y * uk x * um y ∂μ ∂μ := by
    unfold fp81s21_initialCancel_Qk
    exact integral_prod _ hint
  have hRleb : ∀ x, ∫ y, h x y * uk x * um y ∂μ =
      uk x * ∫ y, fp81s21_initialCancel_rr R um y * h x y := by
    intro x
    have ht := HRS.MS.TcR.tc2_integral_nu E.reference.prob
      (fun y => h x y * uk x * um y)
    refine ht.trans ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [fp81s21_initialCancel_rr]
    ring
  have hQ2 : fp81s21_initialCancel_Qk R φ h k m =
      ∫ x, fp81s21_initialCancel_rr R uk x *
        ∫ y, fp81s21_initialCancel_rr R um y * h x y := by
    rw [hQ1]
    simp_rw [hRleb]
    have ht := HRS.MS.TcR.tc2_integral_nu E.reference.prob
      (fun x => uk x * ∫ y, fp81s21_initialCancel_rr R um y * h x y)
    refine ht.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [fp81s21_initialCancel_rr]
    ring
  have hBχ0' : 0 ≤ Bχ := hBχ1
  have hDc := fp81s21_initialCancel_Dd_bd R E hum1 (by simpa [Bm] using humb)
    (by simpa [Bm] using humd) hv1 hB1 hB2
  set Kk : ℝ := E.C * (Bk + Bk + 1)
  set Km : ℝ := E.C * (Bm + Bm + 1)
  have hKk0 : 0 ≤ Kk := by have hC := E.reference.C0; positivity
  have hKm0 : 0 ≤ Km := by have hC := E.reference.C0; positivity
  have hrk := fp81s21_initialCancel_r_bounds R E huk1 (by simpa [Bk] using hukb)
    (by simpa [Bk] using hukd)
  have hrm := fp81s21_initialCancel_r_bounds R E hum1 (by simpa [Bm] using humb)
    (by simpa [Bm] using humd)
  rcases hrk with ⟨hrk1, hrk0, hrk1'⟩
  rcases hrm with ⟨hrm1, hrm0, hrm1'⟩
  have hrkc : Continuous (fp81s21_initialCancel_rr R uk) := hrk1.continuous
  set Am : Euc p.d → ℝ := fun x =>
    fderiv ℝ (fp81s21_initialCancel_Gpot R um) x (gradient χ x)
  set Ak : Euc p.d → ℝ := fun x =>
    fderiv ℝ (fp81s21_initialCancel_Gpot R uk) x (gradient χ x)
  set Em : Euc p.d → ℝ := fun x =>
    ∫ y, rieszKernel p.d p.s (x - y) *
      fp81s21_initialCancel_Dd R um (gradient χ) y
  have hrow : ∀ x, ∫ y, fp81s21_initialCancel_rr R um y * h x y = Am x - Em x := by
    intro x
    exact fp81s21_initialCancel_row R E hum1 (by simpa [Bm] using humb)
      (by simpa [Bm] using humd) (hGm1.differentiable one_ne_zero) hχ2 hB1 hB2 x
  have hAmc : Continuous Am :=
    (hGm1.continuous_fderiv one_ne_zero).clm_apply hv1.continuous
  have hAkc : Continuous Ak :=
    (hGk1.continuous_fderiv one_ne_zero).clm_apply hv1.continuous
  have hAmb : ∀ x, |Am x| ≤ DGm * Bχ := fun x => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hGmd x) (hB1 x) (norm_nonneg _) hDGm0)
  have hAkb : ∀ x, |Ak x| ≤ DGk * Bχ := fun x => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hGkd x) (hB1 x) (norm_nonneg _) hDGk0)
  have hIA : Integrable (fun x => fp81s21_initialCancel_rr R uk x * Am x) := by
    refine fp81s21_initialCancel_gauss_int R E (hrkc.mul hAmc)
      (K := Kk * (DGm * Bχ)) (fun x => ?_)
    rw [abs_mul]
    calc |fp81s21_initialCancel_rr R uk x| * |Am x| ≤
          (Kk * Real.exp (-E.c * ‖x‖ ^ 2)) * (DGm * Bχ) := by
            exact mul_le_mul (hrk0 x) (hAmb x) (abs_nonneg _) (by positivity)
      _ = Kk * (DGm * Bχ) * Real.exp (-E.c * ‖x‖ ^ 2) := by ring
  obtain ⟨hswap, hIE⟩ := fp81s21_initialCancel_swap R E
    (r := fp81s21_initialCancel_rr R uk) hrkc hKk0 hrk0
    (D := fp81s21_initialCancel_Dd R um (gradient χ)) hDc.1
    (K2 := Km * (Bχ + p.d * Bχ)) (by positivity) hDc.2
  have hQ3 : fp81s21_initialCancel_Qk R φ h k m =
      (∫ x, fp81s21_initialCancel_rr R uk x * Am x) -
        ∫ x, fp81s21_initialCancel_rr R uk x * Em x := by
    rw [hQ2]
    have e : ∀ x, fp81s21_initialCancel_rr R uk x *
        ∫ y, fp81s21_initialCancel_rr R um y * h x y =
        fp81s21_initialCancel_rr R uk x * Am x -
          fp81s21_initialCancel_rr R uk x * Em x := by
      intro x
      rw [hrow x]
      ring
    simp_rw [e]
    exact integral_sub hIA hIE
  have hGk_leb : ∀ y, ∫ x, rieszKernel p.d p.s (y - x) *
      fp81s21_initialCancel_rr R uk x = fp81s21_initialCancel_Gpot R uk y := by
    intro y
    exact (fp81s21_initialCancel_Gpot_leb R E uk y).symm
  have hibp := fp81s21_initialCancel_ibp_div R E hum1 (by simpa [Bm] using humb)
    (by simpa [Bm] using humd) hv1 hB1 hB2 hGk1
    (MH := MGk) hGkb (DH := DGk) hGkd
  have hEm' : ∫ x, fp81s21_initialCancel_rr R uk x * Em x =
      -∫ y, fp81s21_initialCancel_rr R um y * Ak y := by
    rw [hswap]
    simp_rw [hGk_leb]
    exact hibp
  have hQ4 : fp81s21_initialCancel_Qk R φ h k m =
      (∫ x, fp81s21_initialCancel_rr R uk x * Am x) +
        ∫ y, fp81s21_initialCancel_rr R um y * Ak y := by
    rw [hQ3, hEm']
    ring
  have hφd : ∀ i, ContDiff ℝ 1 (φ i) := fun i =>
    (hφ.1 i).1.of_le (by exact_mod_cast
      (by unfold fp81s21_J1; omega : 1 ≤ fp81s21_J1 p.d))
  have hDφ : ∀ i x, ‖fderiv ℝ (φ i) x‖ ≤ cbNorm (fp81s21_J1 p.d) (φ i) :=
    fun i x => s45_cb_deriv_le (by unfold fp81s21_J1; omega) (hφ.1 i) x
  have hbdint : ∀ f : Euc p.d → ℝ, Continuous f → ∀ M : ℝ,
      (∀ x, |f x| ≤ M) → Integrable f μ := fun f hf M hM =>
    Integrable.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact hM x)
  have key : ∀ (i : ℕ) (ua ub : Euc p.d → ℝ) (hua : Continuous ua)
      (Ba : ℝ) (hBa : ∀ x, |ua x| ≤ Ba) (hub : ContDiff ℝ 1 ub)
      (hGu : ContDiff ℝ 1 (fp81s21_initialCancel_Gpot R ub)) (Bb : ℝ)
      (hBb : ∀ x, ‖fderiv ℝ ub x‖ ≤ Bb)
      (hfd : ∀ x e, fderiv ℝ (fp81s21_initialCancel_Gpot R ub) x e =
        p.γ⁻¹ * (fderiv ℝ (φ i) x e - fderiv ℝ ub x e)),
      (∫ x, fp81s21_initialCancel_rr R ua x *
        fderiv ℝ (fp81s21_initialCancel_Gpot R ub) x (gradient χ x)) =
       (∫ x, p.γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x ∂μ) -
       ∫ x, p.γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x ∂μ := by
    intro i ua ub hua Ba hBa hub hGu Bb hBb hfd
    have hBa0 : 0 ≤ Ba := (abs_nonneg _).trans (hBa 0)
    have hBb0 : 0 ≤ Bb := (norm_nonneg _).trans (hBb 0)
    have hP1 : Integrable (fun x => p.γ⁻¹ *
        ⟪gradient χ x, gradient (φ i) x⟫ * ua x) μ := by
      refine hbdint _ ((continuous_const.mul
        (hv1.continuous.inner (s45_gradient_continuous (hφd i)))).mul hua)
        (p.γ⁻¹ * (Bχ * cbNorm (fp81s21_J1 p.d) (φ i)) * Ba) (fun x => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (S99.s99_inner_grad_le hB1 (hDφ i) x)
          (inv_nonneg.2 hγ.le)) (hBa x) (abs_nonneg _)
        (mul_nonneg (inv_nonneg.2 hγ.le)
          (mul_nonneg hBχ0 (HRS.MS.Tc5.tc5_cb_nonneg _ _)))
    have hP2 : Integrable (fun x => p.γ⁻¹ *
        ⟪gradient χ x, gradient ub x⟫ * ua x) μ := by
      refine hbdint _ ((continuous_const.mul
        (hv1.continuous.inner (s45_gradient_continuous hub))).mul hua)
        (p.γ⁻¹ * (Bχ * Bb) * Ba) (fun x => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (S99.s99_inner_grad_le hB1 hBb x)
          (inv_nonneg.2 hγ.le)) (hBa x) (abs_nonneg _) (by positivity)
    have e1 : ∀ x, fp81s21_initialCancel_rr R ua x *
        fderiv ℝ (fp81s21_initialCancel_Gpot R ub) x (gradient χ x) =
        R.ρ 0 x * ((p.γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x) -
          p.γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x) := by
      intro x
      rw [hfd x (gradient χ x)]
      have h1 := HRS.MS.PoisKolm.kl_inner_gradient (φ i) x (gradient χ x)
      have h2 := HRS.MS.PoisKolm.kl_inner_gradient ub x (gradient χ x)
      rw [← h1, ← h2]
      simp only [fp81s21_initialCancel_rr]
      ring
    have ht := HRS.MS.TcR.tc2_integral_nu E.reference.prob
      (fun x => (p.γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x) -
        p.γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x)
    simp_rw [e1]
    rw [← ht]
    exact integral_sub hP1 hP2
  have hkeym := key m uk um huk1.continuous Bk hukb hum1 hGm1 Bm humd hGmfd
  have hkeyk := key k um uk hum1.continuous Bm humb huk1 hGk1 Bk hukd hGkfd
  have hprod1 : ContDiff ℝ 1 (fun x => uk x * um x) := huk1.mul hum1
  have hBprod : ∀ x, |uk x * um x| ≤ Bk * Bm := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hukb x) (humb x) (abs_nonneg _) hBk0
  have hDprod : ∀ x, ‖fderiv ℝ (fun x => uk x * um x) x‖ ≤ Bk * Bm + Bm * Bk := by
    intro x
    have hm : HasFDerivAt (fun x => uk x * um x)
        (uk x • fderiv ℝ um x + um x • fderiv ℝ uk x) x :=
      ((huk1.differentiable one_ne_zero x).hasFDerivAt.mul
        (hum1.differentiable one_ne_zero x).hasFDerivAt)
    rw [hm.fderiv]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hukb x) (humd x) (norm_nonneg _) hBk0
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (humb x) (hukd x) (norm_nonneg _) hBm0
  have hibpmu := fp81s21_initialCancel_ibp_gen R E F j hprod1
    (Bψ := Bk * Bm) (Dψ := Bk * Bm + Bm * Bk) hBprod hDprod
  have hpt : ∀ x, ⟪gradient (fun x => uk x * um x) x, gradient χ x⟫ =
      uk x * ⟪gradient χ x, gradient um x⟫ +
      um x * ⟪gradient χ x, gradient uk x⟫ := by
    intro x
    have hm : HasFDerivAt (fun x => uk x * um x)
        (uk x • fderiv ℝ um x + um x • fderiv ℝ uk x) x :=
      ((huk1.differentiable one_ne_zero x).hasFDerivAt.mul
        (hum1.differentiable one_ne_zero x).hasFDerivAt)
    rw [real_inner_comm, HRS.MS.PoisKolm.kl_inner_gradient, hm.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← HRS.MS.PoisKolm.kl_inner_gradient um x (gradient χ x),
      ← HRS.MS.PoisKolm.kl_inner_gradient uk x (gradient χ x)]
  have hI2k : Integrable (fun x => p.γ⁻¹ *
      ⟪gradient χ x, gradient um x⟫ * uk x) μ := by
    refine hbdint _ ((continuous_const.mul
      (hv1.continuous.inner (s45_gradient_continuous hum1))).mul huk1.continuous)
      (p.γ⁻¹ * (Bχ * Bm) * Bk) (fun x => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (S99.s99_inner_grad_le hB1 humd x)
        (inv_nonneg.2 hγ.le)) (hukb x) (abs_nonneg _) (by positivity)
  have hI2m : Integrable (fun x => p.γ⁻¹ *
      ⟪gradient χ x, gradient uk x⟫ * um x) μ := by
    refine hbdint _ ((continuous_const.mul
      (hv1.continuous.inner (s45_gradient_continuous huk1))).mul hum1.continuous)
      (p.γ⁻¹ * (Bχ * Bk) * Bm) (fun x => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (S99.s99_inner_grad_le hB1 hukd x)
        (inv_nonneg.2 hγ.le)) (humb x) (abs_nonneg _) (by positivity)
  have hsum2 : (∫ x, p.γ⁻¹ * ⟪gradient χ x, gradient um x⟫ * uk x ∂μ) +
      (∫ x, p.γ⁻¹ * ⟪gradient χ x, gradient uk x⟫ * um x ∂μ) =
      ∫ x, r26t3_a R (φ j) x * uk x * um x ∂μ := by
    rw [← integral_add hI2k hI2m]
    have e3 : ∀ x, p.γ⁻¹ * ⟪gradient χ x, gradient um x⟫ * uk x +
        p.γ⁻¹ * ⟪gradient χ x, gradient uk x⟫ * um x =
        p.γ⁻¹ * ⟪gradient (fun x => uk x * um x) x, gradient χ x⟫ := by
      intro x
      rw [hpt x]
      ring
    simp_rw [e3]
    rw [integral_const_mul, ← hibpmu]
    have e4 : ∀ x, (uk x * um x) * (p.γ * r26t3_a R (φ j) x) =
        p.γ * (r26t3_a R (φ j) x * uk x * um x) := by
      intro x
      ring
    simp_rw [e4]
    rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]
  have hcc : ∀ i i' : ℕ,
      fp81s21_initialCancel_cc R F j i i' =
        ∫ x, p.γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ *
          r26t3_a R (φ i') x ∂μ := by
    intro i i'
    rfl
  rw [hQ4, hkeym, hkeyk, hcc k m, hcc m k]
  rw [← hsum2]
  ring

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initialCancel_cancel
