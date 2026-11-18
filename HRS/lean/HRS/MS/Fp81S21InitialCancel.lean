import HRS.MS.Fp81S21InitialFam2
import HRS.MS.R2SeAux37

/-!
# S2.1(iii), packet 25a: actual-initial-law cancellation prerequisites

Thermal target being ported (`S99.s99_cancel`, `R2SeAux37.lean:74`): for
`cc(j,k,m) = ∫ w_{jk} a_m dμ`, `Qk(h;k,m) = ∬ h(x,y) a_k(x) a_m(y) dμ(x)dμ(y)`,
and `h = commutatorKernel d s (gradient (χ_j))`,

```
cc(j,k,m) + cc(j,m,k) - Qk(h;k,m) = ∫ a_j a_k a_m dμ.
```

Dependency port inventory (thermal lemma → status at `μ = r26t3_mu R 0`):

* `s99_conv_cont`: actual-law version needed; the Gaussian envelope in `E.reference`
  gives the same kernel-convolution continuity argument.
* `s99_resp_all`: actual-law version available from `r26t3_response_smooth`;
  `fp81s21_initialCancel_response_all` exposes it.
* `s99_Gpot_eq`, `s99_ua`: actual-law versions needed; the response equation,
  `InitialFamData.amem/anorm`, and `InitialFamData.gen` provide the corresponding data.
* `s99_Gpot_leb`, `s99_r_bounds`, `s99_Gpot_fderiv`: the proofs are generic in
  a positive smooth density with Gaussian bounds, but the thermal statements are
  hard-wired to `thermalDensity`; actual-law versions use `E.reference`.
* `s99_Dd_bd`, `s99_LI_g`, `s99_row`, `s99_swap`, `s99_ibp_div`: actual-law
  versions needed, with the same reference Gaussian bounds and the weighted
  divergence `div((R.ρ 0) v)`; no thermal Euler equation at `ρ⁰` is available.
* `s99_sum_basis`: generic linear-algebra identity, reusable directly.
* `s45_ibp_mu`: thermal Gibbs integration by parts is unavailable at `ρ⁰`;
  the replacement is S47's weighted Gibbs integration by parts from `E.reference`
  (with `∇χ = γ v` retained by `InitialFamData.gen`).

No binder or mathematical statement has been weakened in this port. The response
regularity statement below uses the actual initial law and the existing canonical
response; `E` supplies its smooth positive Gaussian-bounded density.
-/

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

/-- The initial-law response potential, with the actual preparation measure. -/
def fp81s21_initialCancel_Gpot {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (u : Euc p.d → ℝ) : Euc p.d → ℝ :=
  fun x => ∫ y, rieszKernel p.d p.s (x - y) * u y ∂(r26t3_mu R 0)

/-- The density-weighted response used in the divergence calculation. -/
def fp81s21_initialCancel_rr {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (u : Euc p.d → ℝ) (y : Euc p.d) : ℝ :=
  R.ρ 0 y * u y

/-- `div(ρ u v)`, written as the derivative of the weighted vector field. -/
def fp81s21_initialCancel_Dd {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (u : Euc p.d → ℝ) (v : Euc p.d → Euc p.d) (y : Euc p.d) : ℝ :=
  ⟪gradient (fp81s21_initialCancel_rr R u) y, v y⟫ +
    fp81s21_initialCancel_rr R u y * S45.s45_div v y

/-- The actual-law version of the pointwise response equation. -/
theorem fp81s21_initialCancel_response_all
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : ∀ i, MemCb (fp81s21_J1 p.d) (φ i)) (i : ℕ) (x : Euc p.d) :
    r26t3_a R (φ i) x + p.γ * HRS.Whole.Kop (rieszKernel p.d p.s) (r26t3_mu R 0)
      (r26t3_a R (φ i)) x = HRS.Whole.projMean (r26t3_mu R 0) (φ i) x := by
  obtain ⟨C, hC, hR⟩ := r26t3_response_smooth hδ hδh R hγ
  exact (hR (φ i) (hφ i)).2.2.2 x

/-- Conversion of the initial-measure integral to a Lebesgue-density integral. -/
theorem fp81s21_initialCancel_Gpot_leb
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    (u : Euc p.d → ℝ) (x : Euc p.d) :
    fp81s21_initialCancel_Gpot R u x =
      ∫ y, rieszKernel p.d p.s (x - y) * (R.ρ 0 y * u y) := by
  unfold fp81s21_initialCancel_Gpot r26t3_mu
  rw [HRS.MS.S98.s98_integral_wDR (R.ρ 0)
    E.reference.smooth.continuous.measurable
    (fun y => (E.reference.pos y).le)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- Gaussian envelope bounds for the actual weighted density `ρ⁰ u`. -/
theorem fp81s21_initialCancel_r_bounds
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {u : Euc p.d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ}
    (hBu : ∀ x, |u x| ≤ Bu) (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du) :
    ContDiff ℝ 1 (fp81s21_initialCancel_rr R u) ∧
    (∀ y, |fp81s21_initialCancel_rr R u y| ≤
      (E.C * (Bu + Du + 1)) * Real.exp (-E.c * ‖y‖ ^ 2)) ∧
    (∀ y, ‖fderiv ℝ (fp81s21_initialCancel_rr R u) y‖ ≤
      (E.C * (Bu + Du + 1)) * Real.exp (-E.c * ‖y‖ ^ 2)) := by
  have hρ1 : ContDiff ℝ 1 (R.ρ 0) := E.reference.smooth.of_le (by exact_mod_cast le_top)
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  refine ⟨hρ1.mul hu, ?_, ?_⟩
  · intro y
    rw [fp81s21_initialCancel_rr, abs_mul, abs_of_pos (E.reference.pos y)]
    have h0 : R.ρ 0 y ≤ E.C * Real.exp (-E.c * ‖y‖ ^ 2) := by
      simpa [abs_of_pos (E.reference.pos y)] using E.reference.h0 y
    calc R.ρ 0 y * |u y| ≤ (E.C * Real.exp (-E.c * ‖y‖ ^ 2)) * Bu :=
          mul_le_mul h0 (hBu y) (abs_nonneg _) (mul_nonneg E.reference.C0 (Real.exp_pos _).le)
      _ ≤ (E.C * (Bu + Du + 1)) * Real.exp (-E.c * ‖y‖ ^ 2) := by
          have he := (Real.exp_pos (-E.c * ‖y‖ ^ 2)).le
          have hC := E.reference.C0
          nlinarith [mul_nonneg hC (he), mul_nonneg hC (mul_nonneg he (by linarith : 0 ≤ Du + 1))]
  · intro y
    have hρd : DifferentiableAt ℝ (R.ρ 0) y := (hρ1.differentiable (by norm_num)) y
    have hud : DifferentiableAt ℝ u y := (hu.differentiable (by norm_num)) y
    have hm : HasFDerivAt (fun z => R.ρ 0 z * u z)
        (R.ρ 0 y • fderiv ℝ u y + u y • fderiv ℝ (R.ρ 0) y) y := hρd.hasFDerivAt.mul hud.hasFDerivAt
    change ‖fderiv ℝ (fun z => R.ρ 0 z * u z) y‖ ≤ _
    rw [hm.fderiv]
    have h0 : R.ρ 0 y ≤ E.C * Real.exp (-E.c * ‖y‖ ^ 2) := by
      simpa [abs_of_pos (E.reference.pos y)] using E.reference.h0 y
    have he := (Real.exp_pos (-E.c * ‖y‖ ^ 2)).le
    have e1 : ‖R.ρ 0 y • fderiv ℝ u y‖ ≤
        (E.C * Real.exp (-E.c * ‖y‖ ^ 2)) * Du := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (E.reference.pos y)]
      exact mul_le_mul h0 (hDu y) (norm_nonneg _) (mul_nonneg E.reference.C0 he)
    have e2 : ‖u y • fderiv ℝ (R.ρ 0) y‖ ≤ Bu * (E.C * Real.exp (-E.c * ‖y‖ ^ 2)) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hBu y) (E.reference.h1 y) (norm_nonneg _) hBu0
    refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
    have hC := E.reference.C0
    nlinarith [mul_nonneg hC he, mul_nonneg hC (mul_nonneg he (by linarith : 0 ≤ Du + 1))]

/-- Differentiate the actual-law convolution by moving the derivative onto `ρ⁰u`.

This is the nonthermal counterpart of `S99.s99_Gpot_fderiv`; its proof uses only
the density bounds in `InitialSteinEnv.reference`. -/
theorem fp81s21_initialCancel_Gpot_fderiv
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {u : Euc p.d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ}
    (hBu : ∀ x, |u x| ≤ Bu) (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du)
    (hdiff : Differentiable ℝ (fp81s21_initialCancel_Gpot R u))
    (x e : Euc p.d) (he : ‖e‖ ≤ 1) :
    fderiv ℝ (fp81s21_initialCancel_Gpot R u) x e =
      ∫ y, rieszKernel p.d p.s (x - y) *
        fderiv ℝ (fp81s21_initialCancel_rr R u) y e := by
  obtain ⟨hr1, hr0, hr1'⟩ := fp81s21_initialCancel_r_bounds R E hu hBu hDu
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hd : 2 ≤ p.d := p.hd
  have hC' : 0 ≤ E.C * (Bu + Du + 1) := by
    have hC := E.reference.C0
    positivity
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith [p.hs]
  have hgm : Measurable (rieszKernel p.d p.s) := S47.s47_kernel_measurable p.s
  have hA := movtr_hasDerivAt_conv (c := E.c) E.reference.hc (k := rieszKernel p.d p.s)
    (B := fun z => 2 * ‖z‖ ^ (-movtr_sp p.s) + ‖z‖ + 1) hgm.aestronglyMeasurable
    (by
      filter_upwards [movtr_ae_ne_zero (d := p.d) (by omega)] with z hz
      rw [← movtr_gEps_zero p.d p.s]
      exact movtr_gEps_abs_le p.hs0 le_rfl zero_le_one hz)
    (movtr_majorant_integrable (by omega) p.hs0 hsd
      (c := E.c / 2) (by have := E.reference.hc; positivity)) hC' hr1 hr0 hr1' x e he
  have hfun : (fun t : ℝ => ∫ z, rieszKernel p.d p.s z *
      fp81s21_initialCancel_rr R u (x + t • e - z)) =
      fun t => fp81s21_initialCancel_Gpot R u (x + t • e) := by
    funext t
    rw [fp81s21_initialCancel_Gpot_leb R E u (x + t • e),
      ← integral_sub_left_eq_self
        (fun y => rieszKernel p.d p.s (x + t • e - y) *
          (R.ρ 0 y * u y)) (volume : Measure (Euc p.d)) (x + t • e)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [fp81s21_initialCancel_rr, sub_sub_cancel]
  rw [hfun] at hA
  have hline : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    have ht := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    simpa using ht
  have hB := (hdiff (x + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
  have hEq := hA.unique hB
  simp only [zero_smul, add_zero] at hEq
  rw [← hEq]
  rw [← integral_sub_left_eq_self
    (fun z => rieszKernel p.d p.s z *
      fderiv ℝ (fp81s21_initialCancel_rr R u) (x - z) e) volume x]
  simp

/-- Actual-law analogue of `S99.s99_ua`: smoothness and uniform pointwise bounds
for the canonical response, its potential, and both first derivatives. -/
theorem fp81s21_initialCancel_ua
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ} (hφ : ∀ i, MemCb (fp81s21_J1 p.d) (φ i))
    (F : InitialFamData R φ) (i : ℕ) :
    ContDiff ℝ 1 (r26t3_a R (φ i)) ∧
    (∀ x, |r26t3_a R (φ i) x| ≤ F.K * cbNorm (fp81s21_J1 p.d) (φ i)) ∧
    (∀ x, ‖fderiv ℝ (r26t3_a R (φ i)) x‖ ≤
      F.K * cbNorm (fp81s21_J1 p.d) (φ i)) ∧
    ContDiff ℝ 1 (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) ∧
    (∃ MG : ℝ, ∀ x, |fp81s21_initialCancel_Gpot R (r26t3_a R (φ i)) x| ≤ MG) ∧
    (∃ DG : ℝ, ∀ x, ‖fderiv ℝ
      (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) x‖ ≤ DG) ∧
    (∀ x e, fderiv ℝ (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) x e =
      p.γ⁻¹ * (fderiv ℝ (φ i) x e - fderiv ℝ (r26t3_a R (φ i)) x e)) := by
  have hJ : 1 ≤ fp81s21_J1 p.d := by unfold fp81s21_J1; omega
  have hk : 1 ≤ fp81s21_k0 p.d := fp81s21_k0_ge_one p.d
  have hu : ContDiff ℝ 1 (r26t3_a R (φ i)) :=
    (F.amem i).1.of_le (by exact_mod_cast hk)
  have hb : ∀ x, |r26t3_a R (φ i) x| ≤ F.K * cbNorm (fp81s21_J1 p.d) (φ i) := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le (F.amem i) x
    have habs : |r26t3_a R (φ i) x| ≤ cbNorm (fp81s21_k0 p.d) (r26t3_a R (φ i)) := by
      simpa [Real.norm_eq_abs] using h
    exact habs.trans (F.anorm i)
  have hd : ∀ x, ‖fderiv ℝ (r26t3_a R (φ i)) x‖ ≤
      F.K * cbNorm (fp81s21_J1 p.d) (φ i) := by
    intro x
    exact (S45.s45_cb_deriv_le hk (F.amem i) x).trans (F.anorm i)
  have hφ1 : ContDiff ℝ 1 (φ i) := (hφ i).1.of_le (by exact_mod_cast hJ)
  have hφb : ∀ x, |φ i x| ≤ cbNorm (fp81s21_J1 p.d) (φ i) := by
    intro x
    have h := HRS.MS.Tc5.tc5_cb_sup_le (hφ i) x
    simpa [Real.norm_eq_abs] using h
  have hφd : ∀ x, ‖fderiv ℝ (φ i) x‖ ≤ cbNorm (fp81s21_J1 p.d) (φ i) :=
    fun x => S45.s45_cb_deriv_le hJ (hφ i) x
  obtain ⟨C, hC, hresp⟩ := r26t3_response_smooth hδ hδh R hγ
  have hall := (hresp (φ i) (hφ i)).2.2.2
  let c₀ : ℝ := HRS.Whole.pair (r26t3_mu R 0)
      (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) -
        p.γ⁻¹ * HRS.Whole.pair (r26t3_mu R 0) (φ i)
  have hGe : fp81s21_initialCancel_Gpot R (r26t3_a R (φ i)) =
      fun x => c₀ + p.γ⁻¹ * (φ i x - r26t3_a R (φ i) x) := by
    funext x
    have hk : HRS.Whole.Kop (rieszKernel p.d p.s) (r26t3_mu R 0)
        (r26t3_a R (φ i)) x =
        fp81s21_initialCancel_Gpot R (r26t3_a R (φ i)) x -
          HRS.Whole.pair (r26t3_mu R 0)
            (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) := by
      simp [HRS.Whole.Kop, HRS.Whole.projMean, HRS.Whole.pair,
        fp81s21_initialCancel_Gpot]
    have hallx := hall x
    rw [hk] at hallx
    have hγ0 : p.γ ≠ 0 := hγ.ne'
    simp only [HRS.Whole.projMean] at hallx
    dsimp [c₀]
    field_simp [hγ0]
    linarith [hallx]
  have hG1 : ContDiff ℝ 1 (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) := by
    rw [hGe]
    exact contDiff_const.add (contDiff_const.mul (hφ1.sub hu))
  have hder : ∀ x, HasFDerivAt (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i)))
      (p.γ⁻¹ • (fderiv ℝ (φ i) x - fderiv ℝ (r26t3_a R (φ i)) x)) x := by
    intro x
    rw [hGe]
    exact (((hφ1.differentiable one_ne_zero x).hasFDerivAt.sub
      (hu.differentiable one_ne_zero x).hasFDerivAt).const_mul p.γ⁻¹).const_add c₀
  have hfd : ∀ x e, fderiv ℝ (fp81s21_initialCancel_Gpot R (r26t3_a R (φ i))) x e =
      p.γ⁻¹ * (fderiv ℝ (φ i) x e - fderiv ℝ (r26t3_a R (φ i)) x e) := by
    intro x e
    rw [(hder x).fderiv]
    simp
  have hbφ0 : 0 ≤ cbNorm (fp81s21_J1 p.d) (φ i) :=
    HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hBk0 : 0 ≤ F.K * cbNorm (fp81s21_J1 p.d) (φ i) := mul_nonneg F.hK hbφ0
  refine ⟨hu, hb, hd, hG1,
    ⟨|c₀| + p.γ⁻¹ * (cbNorm (fp81s21_J1 p.d) (φ i) +
      F.K * cbNorm (fp81s21_J1 p.d) (φ i)), fun x => ?_⟩,
    ⟨p.γ⁻¹ * (cbNorm (fp81s21_J1 p.d) (φ i) +
      F.K * cbNorm (fp81s21_J1 p.d) (φ i)), fun x => ?_⟩, hfd⟩
  · rw [congrFun hGe x]
    calc |c₀ + p.γ⁻¹ * (φ i x - r26t3_a R (φ i) x)| ≤
          |c₀| + |p.γ⁻¹ * (φ i x - r26t3_a R (φ i) x)| := abs_add_le _ _
      _ ≤ |c₀| + p.γ⁻¹ *
          (cbNorm (fp81s21_J1 p.d) (φ i) + F.K * cbNorm (fp81s21_J1 p.d) (φ i)) := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hγ.le)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          ((abs_sub _ _).trans (add_le_add (hφb x) (hb x)))
          (inv_nonneg.2 hγ.le))
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun e => ?_
    rw [hfd x e, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (inv_nonneg.2 hγ.le)]
    have h1 : |fderiv ℝ (φ i) x e| ≤
        cbNorm (fp81s21_J1 p.d) (φ i) * ‖e‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hφd x) (norm_nonneg _))
    have h2 : |fderiv ℝ (r26t3_a R (φ i)) x e| ≤
        (F.K * cbNorm (fp81s21_J1 p.d) (φ i)) * ‖e‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hd x) (norm_nonneg _))
    calc p.γ⁻¹ * |fderiv ℝ (φ i) x e - fderiv ℝ (r26t3_a R (φ i)) x e|
        ≤ p.γ⁻¹ * (cbNorm (fp81s21_J1 p.d) (φ i) * ‖e‖ +
          (F.K * cbNorm (fp81s21_J1 p.d) (φ i)) * ‖e‖) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2))
            (inv_nonneg.2 hγ.le)
      _ = p.γ⁻¹ * (cbNorm (fp81s21_J1 p.d) (φ i) +
          F.K * cbNorm (fp81s21_J1 p.d) (φ i)) * ‖e‖ := by ring

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initialCancel_response_all
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_Gpot_leb
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_r_bounds
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_Gpot_fderiv
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_ua
