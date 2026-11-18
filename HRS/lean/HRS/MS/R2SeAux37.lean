import HRS.MS.R2SeAux36

/-!
# S9.9 `r2_static_edgeworth`, packet 37: the cubic cancellation

Worker S99, namespace `S99`.  `s99_cancel`: with `v = ∇χ_j`, `c_{(j,k),m} = ∫ w_{jk} a_m dμ` and
`Q_j(k,m) = ∬ h_{∇χ_j}(x,y) a_k(x) a_m(y) dμ dμ`,
`c_{(j,k),m} + c_{(j,m),k} - Q_j(k,m) = ∫ a_j a_k a_m dμ`.
Proof: `s99_row` (S4.5 one-body integration by parts), the response equation `∇G_i = γ⁻¹ (∇φ_i - ∇a_i)`,
Fubini (`s99_swap`), `s99_ibp_div`, and `s45_ibp_mu` with `L χ_j = γ a_j`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section PotF

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ} (hT : ThermalData d s a β C c BU)

include hd hs0 hsd hT

theorem s99_Dd_bd {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ} (hBu : ∀ x, |u x| ≤ Bu)
    (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) :
    Continuous (Dd (rr d s a β u) (gradient χ)) ∧
    ∀ y, |Dd (rr d s a β u) (gradient χ) y| ≤
      (C * (Bu + Du + 1)) * (B1 + d * B2) * Real.exp (-c * ‖y‖ ^ 2) := by
  obtain ⟨hr1, hr0, hr1'⟩ := s99_r_bounds hd hs0 hsd hT hu hBu hDu
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
  have hC' : 0 ≤ C * (Bu + Du + 1) := by have := hT.C0; positivity
  have hexp := fun y : Euc d => (Real.exp_pos (-c * ‖y‖ ^ 2)).le
  refine ⟨?_, fun y => ?_⟩
  · unfold Dd
    exact ((s45_gradient_continuous hr1).inner hv1.continuous).add
      (hr1.continuous.mul (s45_continuous_div hv1))
  · unfold Dd
    have e1 : |⟪gradient (rr d s a β u) y, gradient χ y⟫| ≤ (C * (Bu + Du + 1) * Real.exp (-c * ‖y‖ ^ 2)) * B1 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [s45_norm_gradient]
      exact mul_le_mul (hr1' y) (hB1 y) (norm_nonneg _) (by have := hexp y; positivity)
    have e2 : |rr d s a β u y * s45_div (gradient χ) y| ≤
        (C * (Bu + Du + 1) * Real.exp (-c * ‖y‖ ^ 2)) * (d * B2) := by
      rw [abs_mul]
      exact mul_le_mul (hr0 y) (s45_div_le hB2 y) (abs_nonneg _) (by have := hexp y; positivity)
    refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    ring

end PotF

section Cancel

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

set_option maxHeartbeats 4000000 in
theorem s99_cancel (j k m : ℕ) :
    cc d s a β γ F (j, k) m + cc d s a β γ F (j, m) k -
        Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) k m =
      ∫ x, aRep d s a β γ (φ j) x * aRep d s a β γ (φ k) x * aRep d s a β γ (φ m) x
        ∂(thermalMeasure d s a β) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hC0 := hT.C0
  have hc0 := hT.hc
  set μ := thermalMeasure d s a β with hμdef
  have hwf := F.feat hT hγ j
  set χ := F.χ j with hχdef
  set Bχ : ℝ := F.K * cbNorm (J1 d) (φ j) with hBχ
  have hχ2 : ContDiff ℝ 2 χ := hwf.smooth
  have hB1 : ∀ x, ‖gradient χ x‖ ≤ Bχ := hwf.B1
  have hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ Bχ := hwf.B2
  have hBχ0 : 0 ≤ Bχ := (norm_nonneg _).trans (hB1 0)
  have hv1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ2
  obtain ⟨huk1, hukb, hukd, hGk1, ⟨MGk, hGkb⟩, ⟨DGk, hGkd⟩, hGkfd⟩ := s99_ua hd hs0 hs ha hβ hγ hT hφ F k
  obtain ⟨hum1, humb, humd, hGm1, ⟨MGm, hGmb⟩, ⟨DGm, hGmd⟩, hGmfd⟩ := s99_ua hd hs0 hs ha hβ hγ hT hφ F m
  set uk := aRep d s a β γ (φ k) with hukdef
  set um := aRep d s a β γ (φ m) with humdef
  set Bk : ℝ := F.K * cbNorm (J1 d) (φ k) with hBk
  set Bm : ℝ := F.K * cbNorm (J1 d) (φ m) with hBm
  have hBk0 : 0 ≤ Bk := (abs_nonneg _).trans (hukb 0)
  have hBm0 : 0 ≤ Bm := (abs_nonneg _).trans (humb 0)
  have hDGk0 : 0 ≤ DGk := (norm_nonneg _).trans (hGkd 0)
  have hDGm0 : 0 ≤ DGm := (norm_nonneg _).trans (hGmd 0)
  have hMGk0 : 0 ≤ MGk := (abs_nonneg _).trans (hGkb 0)
  have hMGm0 : 0 ≤ MGm := (abs_nonneg _).trans (hGmb 0)
  -- the kernel
  set Λ : ℝ≥0 := ⟨Bχ, hBχ0⟩ with hΛdef
  have hvd : Differentiable ℝ (gradient χ) := hv1.differentiable one_ne_zero
  have hLip : LipschitzWith Λ (gradient χ) := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hker := s99_comm_isBounded (d := d) hs0 Λ hLip
  have hwr8 := s99_kernel_wr8 hd hs0 hs ha hβ hγ hT hS hker
  set h := commutatorKernel d s (gradient χ) with hhdef
  -- Step 1: `Q` as an iterated integral
  have hwc : Continuous (fun p : Euc d × Euc d => uk p.1 * um p.2) :=
    (huk1.continuous.comp continuous_fst).mul (hum1.continuous.comp continuous_snd)
  have hint : Integrable (fun p : Euc d × Euc d => h p.1 p.2 * uk p.1 * um p.2) (μ.prod μ) := by
    have := hwr8.prod.bdd_mul (f := fun p : Euc d × Euc d => uk p.1 * um p.2) (c := Bk * Bm)
      hwc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hukb _) (humb _) (abs_nonneg _) hBk0)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    show uk p.1 * um p.2 * h p.1 p.2 = h p.1 p.2 * uk p.1 * um p.2
    ring
  have hQ1 : Qk d s a β γ φ h k m = ∫ x, ∫ y, h x y * uk x * um y ∂μ ∂μ := by
    unfold Qk
    exact integral_prod _ hint
  have hRleb : ∀ x, ∫ y, h x y * uk x * um y ∂μ = uk x * ∫ y, rr d s a β um y * h x y := by
    intro x
    have := HRS.MS.TcR.tc2_integral_nu hT.prob (fun y => h x y * uk x * um y)
    refine this.trans ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [rr]; ring
  have hQ2 : Qk d s a β γ φ h k m = ∫ x, rr d s a β uk x * ∫ y, rr d s a β um y * h x y := by
    rw [hQ1]
    simp_rw [hRleb]
    have := HRS.MS.TcR.tc2_integral_nu hT.prob (fun x => uk x * ∫ y, rr d s a β um y * h x y)
    refine this.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [rr]; ring
  -- Step 2: the row identity
  obtain ⟨hrk1, hrk0, hrk1'⟩ := s99_r_bounds hd hs0 hsd hT huk1 hukb hukd
  obtain ⟨hrm1, hrm0, hrm1'⟩ := s99_r_bounds hd hs0 hsd hT hum1 humb humd
  obtain ⟨hDc, hDb⟩ := s99_Dd_bd hd hs0 hsd hT hum1 humb humd hχ2 hB1 hB2
  set Kk : ℝ := C * (Bk + Bk + 1) with hKk
  set Km : ℝ := C * (Bm + Bm + 1) with hKm
  have hKk0 : 0 ≤ Kk := by positivity
  have hKm0 : 0 ≤ Km := by positivity
  have hrkc : Continuous (rr d s a β uk) := hrk1.continuous
  have hexp := fun y : Euc d => (Real.exp_pos (-c * ‖y‖ ^ 2)).le
  set Am : Euc d → ℝ := fun x => fderiv ℝ (Gpot d s a β um) x (gradient χ x) with hAm
  set Ak : Euc d → ℝ := fun x => fderiv ℝ (Gpot d s a β uk) x (gradient χ x) with hAk
  set Em : Euc d → ℝ := fun x => ∫ y, rieszKernel d s (x - y) * Dd (rr d s a β um) (gradient χ) y with hEm
  have hrow : ∀ x, ∫ y, rr d s a β um y * h x y = Am x - Em x := fun x =>
    s99_row hd hs0 hsd hT hum1 humb humd (hGm1.differentiable one_ne_zero) hχ2 hB1 hB2 x
  have hAmc : Continuous Am := (hGm1.continuous_fderiv one_ne_zero).clm_apply hv1.continuous
  have hAkc : Continuous Ak := (hGk1.continuous_fderiv one_ne_zero).clm_apply hv1.continuous
  have hAmb : ∀ x, |Am x| ≤ DGm * Bχ := fun x => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hGmd x) (hB1 x) (norm_nonneg _) hDGm0)
  have hAkb : ∀ x, |Ak x| ≤ DGk * Bχ := fun x => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hGkd x) (hB1 x) (norm_nonneg _) hDGk0)
  have hIA : Integrable (fun x => rr d s a β uk x * Am x) := by
    refine s99_gauss_int hd hs0 hsd hT (hrkc.mul hAmc) (K := Kk * (DGm * Bχ)) (fun y => ?_)
    rw [abs_mul]
    calc |rr d s a β uk y| * |Am y| ≤ (Kk * Real.exp (-c * ‖y‖ ^ 2)) * (DGm * Bχ) :=
          mul_le_mul (hrk0 y) (hAmb y) (abs_nonneg _) (by have := hexp y; positivity)
      _ = _ := by ring
  obtain ⟨hswap, hIE⟩ := s99_swap hd hs0 hsd hT (r := rr d s a β uk) hrkc hKk0 hrk0
    (D := Dd (rr d s a β um) (gradient χ)) hDc (K2 := Km * (Bχ + d * Bχ)) (by positivity) hDb
  have hQ3 : Qk d s a β γ φ h k m = (∫ x, rr d s a β uk x * Am x) - ∫ x, rr d s a β uk x * Em x := by
    rw [hQ2]
    have e : ∀ x, rr d s a β uk x * ∫ y, rr d s a β um y * h x y =
        rr d s a β uk x * Am x - rr d s a β uk x * Em x := fun x => by rw [hrow x]; ring
    simp_rw [e]
    exact integral_sub hIA hIE
  -- Step 3: Fubini and integration by parts
  have hGk_leb : ∀ y, ∫ x, rieszKernel d s (y - x) * rr d s a β uk x = Gpot d s a β uk y := fun y =>
    (s99_Gpot_leb hd hs0 hsd hT uk y).symm
  have hibp := s99_ibp_div hd hs0 hsd hT (r := rr d s a β um) hrm1 hKm0 hrm0 hrm1' hv1 hB1 hB2 hGk1
    (MH := MGk) hGkb (DH := DGk) hGkd
  have hEm' : ∫ x, rr d s a β uk x * Em x = -∫ y, rr d s a β um y * Ak y := by
    rw [hswap]
    simp_rw [hGk_leb]
    exact hibp
  have hQ4 : Qk d s a β γ φ h k m = (∫ x, rr d s a β uk x * Am x) + ∫ y, rr d s a β um y * Ak y := by
    rw [hQ3, hEm']; ring
  -- Step 4: conversion to `μ`-integrals
  have hφd : ∀ i, ContDiff ℝ 1 (φ i) := fun i => (hφ.1 i).1.of_le (by exact_mod_cast (by unfold J1; omega : 1 ≤ J1 d))
  have hDφ : ∀ i x, ‖fderiv ℝ (φ i) x‖ ≤ cbNorm (J1 d) (φ i) := fun i x =>
    s45_cb_deriv_le (by unfold J1; omega) (hφ.1 i) x
  have hbdint : ∀ f : Euc d → ℝ, Continuous f → ∀ M : ℝ, (∀ x, |f x| ≤ M) → Integrable f μ :=
    fun f hf M hM => Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  -- the general conversion
  have key : ∀ (i : ℕ) (ua ub : Euc d → ℝ) (hua : Continuous ua) (Ba : ℝ) (hBa : ∀ x, |ua x| ≤ Ba)
      (hub : ContDiff ℝ 1 ub) (hGu : ContDiff ℝ 1 (Gpot d s a β ub)) (Bb : ℝ) (hBb : ∀ x, ‖fderiv ℝ ub x‖ ≤ Bb)
      (hfd : ∀ x e, fderiv ℝ (Gpot d s a β ub) x e = γ⁻¹ * (fderiv ℝ (φ i) x e - fderiv ℝ ub x e)),
      (∫ x, rr d s a β ua x * fderiv ℝ (Gpot d s a β ub) x (gradient χ x)) =
        (∫ x, γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x ∂μ) -
          ∫ x, γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x ∂μ := by
    intro i ua ub hua Ba hBa hub hGu Bb hBb hfd
    have hBa0 : 0 ≤ Ba := (abs_nonneg _).trans (hBa 0)
    have hBb0 : 0 ≤ Bb := (norm_nonneg _).trans (hBb 0)
    have hP1 : Integrable (fun x => γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x) μ := by
      refine hbdint _ ((continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous (hφd i)))).mul hua)
        (γ⁻¹ * (Bχ * cbNorm (J1 d) (φ i)) * Ba) (fun x => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (s99_inner_grad_le hB1 (hDφ i) x) (inv_nonneg.2 hγ.le))
        (hBa x) (abs_nonneg _) (mul_nonneg (inv_nonneg.2 hγ.le) (mul_nonneg hBχ0 (HRS.MS.Tc5.tc5_cb_nonneg _ _)))
    have hP2 : Integrable (fun x => γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x) μ := by
      refine hbdint _ ((continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous hub))).mul hua)
        (γ⁻¹ * (Bχ * Bb) * Ba) (fun x => ?_)
      rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (s99_inner_grad_le hB1 hBb x) (inv_nonneg.2 hγ.le))
        (hBa x) (abs_nonneg _) (by positivity)
    have e1 : ∀ x, rr d s a β ua x * fderiv ℝ (Gpot d s a β ub) x (gradient χ x) =
        thermalDensity d s a β x * ((γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x) -
          γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x) := by
      intro x
      rw [hfd x (gradient χ x)]
      have h1 := HRS.MS.PoisKolm.kl_inner_gradient (φ i) x (gradient χ x)
      have h2 := HRS.MS.PoisKolm.kl_inner_gradient ub x (gradient χ x)
      rw [← h1, ← h2]
      simp only [rr]; ring
    have e2 := HRS.MS.TcR.tc2_integral_nu hT.prob (fun x => (γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ * ua x) -
          γ⁻¹ * ⟪gradient χ x, gradient ub x⟫ * ua x)
    simp_rw [e1]
    show ∫ x, thermalDensity d s a β x * _ = _
    rw [← e2]
    exact integral_sub hP1 hP2
  have hkey_m := key m uk um huk1.continuous Bk hukb hum1 hGm1 Bm humd hGmfd
  have hkey_k := key k um uk hum1.continuous Bm humb huk1 hGk1 Bk hukd hGkfd
  -- Step 5: the final integration by parts against `μ`
  have hprod1 : ContDiff ℝ 1 (fun x => uk x * um x) := huk1.mul hum1
  have hibpmu := s45_ibp_mu hT hχ2 hB1 hB2 (φ := fun x => uk x * um x) hprod1 (Bφ := Bk * Bm)
    (Dφ := Bk * Bm + Bm * Bk) (fun x => by
      rw [abs_mul]; exact mul_le_mul (hukb x) (humb x) (abs_nonneg _) hBk0) (fun x => by
      have hm : HasFDerivAt (fun x => uk x * um x) (uk x • fderiv ℝ um x + um x • fderiv ℝ uk x) x :=
        ((huk1.differentiable one_ne_zero x).hasFDerivAt.mul (hum1.differentiable one_ne_zero x).hasFDerivAt)
      rw [hm.fderiv]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (hukb x) (humd x) (norm_nonneg _) hBk0
      · rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul (humb x) (hukd x) (norm_nonneg _) hBm0)
  have hpt : ∀ x, ⟪gradient (fun x => uk x * um x) x, gradient χ x⟫ =
      uk x * ⟪gradient χ x, gradient um x⟫ + um x * ⟪gradient χ x, gradient uk x⟫ := by
    intro x
    have hm : HasFDerivAt (fun x => uk x * um x) (uk x • fderiv ℝ um x + um x • fderiv ℝ uk x) x :=
      ((huk1.differentiable one_ne_zero x).hasFDerivAt.mul (hum1.differentiable one_ne_zero x).hasFDerivAt)
    rw [real_inner_comm, HRS.MS.PoisKolm.kl_inner_gradient, hm.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← HRS.MS.PoisKolm.kl_inner_gradient um x (gradient χ x),
      ← HRS.MS.PoisKolm.kl_inner_gradient uk x (gradient χ x)]
  have hI2k : Integrable (fun x => γ⁻¹ * ⟪gradient χ x, gradient um x⟫ * uk x) μ :=
    hbdint _ ((continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous hum1))).mul huk1.continuous)
      (γ⁻¹ * (Bχ * Bm) * Bk) (fun x => by
        rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (s99_inner_grad_le hB1 humd x) (inv_nonneg.2 hγ.le))
          (hukb x) (abs_nonneg _) (by positivity))
  have hI2m : Integrable (fun x => γ⁻¹ * ⟪gradient χ x, gradient uk x⟫ * um x) μ :=
    hbdint _ ((continuous_const.mul (hv1.continuous.inner (s45_gradient_continuous huk1))).mul hum1.continuous)
      (γ⁻¹ * (Bχ * Bk) * Bm) (fun x => by
        rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (s99_inner_grad_le hB1 hukd x) (inv_nonneg.2 hγ.le))
          (humb x) (abs_nonneg _) (by positivity))
  have hsum2 : (∫ x, γ⁻¹ * ⟪gradient χ x, gradient um x⟫ * uk x ∂μ) +
      (∫ x, γ⁻¹ * ⟪gradient χ x, gradient uk x⟫ * um x ∂μ) =
      ∫ x, aRep d s a β γ (φ j) x * aRep d s a β γ (φ k) x * aRep d s a β γ (φ m) x ∂μ := by
    rw [← integral_add hI2k hI2m]
    have e3 : ∀ x, γ⁻¹ * ⟪gradient χ x, gradient um x⟫ * uk x + γ⁻¹ * ⟪gradient χ x, gradient uk x⟫ * um x =
        γ⁻¹ * ⟪gradient (fun x => uk x * um x) x, gradient χ x⟫ := fun x => by rw [hpt x]; ring
    simp_rw [e3]
    rw [integral_const_mul, ← hibpmu]
    have e4 : ∀ x, (uk x * um x) * thermalGen d s a β χ x =
        γ * (aRep d s a β γ (φ j) x * uk x * um x) := fun x => by rw [F.gen j x]; ring
    simp_rw [e4]
    rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]
  -- assembly
  have hcc : ∀ i i' : ℕ, cc d s a β γ F (j, i) i' = ∫ x, γ⁻¹ * ⟪gradient χ x, gradient (φ i) x⟫ *
      aRep d s a β γ (φ i') x ∂μ := fun i i' => rfl
  rw [hQ4, hkey_m, hkey_k, hcc k m, hcc m k]
  rw [← hsum2]
  ring

end Cancel

end S99

end
