import HRS.MS.Fp81S21InitialCancel2

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

/-- Gaussian-envelope integration for the actual reference rate in `E`. -/
theorem fp81s21_initialCancel_gauss_int
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {f : Euc p.d → ℝ} (hf : Continuous f) {K : ℝ}
    (hb : ∀ y, |f y| ≤ K * Real.exp (-E.c * ‖y‖ ^ 2)) : Integrable f := by
  refine Integrable.mono' ((HRS.MP.SelfSimP4Impl.p4g_integrable_gauss p.d E.reference.hc).const_mul K)
    hf.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  simpa [neg_mul] using hb y

/-- Riesz convolution of an actual Gaussian-bounded Lebesgue density is integrable. -/
theorem fp81s21_initialCancel_LI_g
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {h : Euc p.d → ℝ} (hh : Continuous h) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ y, |h y| ≤ K * Real.exp (-E.c * ‖y‖ ^ 2)) (x : Euc p.d) :
    Integrable (fun y => rieszKernel p.d p.s (x - y) * h y) := by
  have hd : 2 ≤ p.d := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith [p.hs]
  have hgm : Measurable (rieszKernel p.d p.s) := S47.s47_kernel_measurable p.s
  have hkB : ∀ z : Euc p.d, z ≠ 0 → |rieszKernel p.d p.s z| ≤
      1 * (2 * ‖z‖ ^ (-movtr_sp p.s) + ‖z‖ + 1) := by
    intro z hz
    rw [one_mul, ← movtr_gEps_zero p.d p.s]
    exact movtr_gEps_abs_le p.hs0 le_rfl zero_le_one hz
  exact s45_LI (by omega) p.hs0 hsd E.reference.hc (k := rieszKernel p.d p.s)
    (h := h) hgm.aestronglyMeasurable hh zero_le_one hkB hK hb x

/-- Actual-law bound on the commutator divergence, parallel to `s99_Dd_bd`. -/
theorem fp81s21_initialCancel_Dd_bd
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {u : Euc p.d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ}
    (hBu : ∀ x, |u x| ≤ Bu) (hDu : ∀ x, ‖fderiv ℝ u x‖ ≤ Du)
    {v : Euc p.d → Euc p.d} (hv : ContDiff ℝ 1 v) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖v x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ v x‖ ≤ B2) :
    Continuous (fp81s21_initialCancel_Dd R u v) ∧
    (∀ y, |fp81s21_initialCancel_Dd R u v y| ≤
      (E.C * (Bu + Du + 1)) * (B1 + p.d * B2) * Real.exp (-E.c * ‖y‖ ^ 2)) := by
  obtain ⟨hr1, hr0, hr1'⟩ := fp81s21_initialCancel_r_bounds R E hu hBu hDu
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hv1 : ContDiff ℝ 1 v := hv
  have hC' : 0 ≤ E.C * (Bu + Du + 1) := by
    have hC := E.reference.C0
    positivity
  have hexp := fun y : Euc p.d => (Real.exp_pos (-E.c * ‖y‖ ^ 2)).le
  refine ⟨?_, fun y => ?_⟩
  · unfold fp81s21_initialCancel_Dd
    exact ((s45_gradient_continuous hr1).inner hv1.continuous).add
      (hr1.continuous.mul (s45_continuous_div hv1))
  · unfold fp81s21_initialCancel_Dd
    have e1 : |⟪gradient (fp81s21_initialCancel_rr R u) y, v y⟫| ≤
        (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) * B1 := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [s45_norm_gradient]
      exact mul_le_mul (hr1' y) (hB1 y) (norm_nonneg _)
        (by have := hexp y; positivity)
    have e2 : |fp81s21_initialCancel_rr R u y * s45_div v y| ≤
        (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) * (p.d * B2) := by
      rw [abs_mul]
      exact mul_le_mul (hr0 y) (s45_div_le hB2 y) (abs_nonneg _)
        (by have := hexp y; positivity)
    refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    ring

/-- Swap the two Riesz convolutions for functions with the actual Gaussian rate. -/
theorem fp81s21_initialCancel_swap
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {r D : Euc p.d → ℝ} (hr : Continuous r) {K1 : ℝ} (hK1 : 0 ≤ K1)
    (hrb : ∀ y, |r y| ≤ K1 * Real.exp (-E.c * ‖y‖ ^ 2))
    (hD : Continuous D) {K2 : ℝ} (hK2 : 0 ≤ K2)
    (hDb : ∀ y, |D y| ≤ K2 * Real.exp (-E.c * ‖y‖ ^ 2)) :
    (∫ x, r x * ∫ y, rieszKernel p.d p.s (x - y) * D y =
      ∫ y, D y * ∫ x, rieszKernel p.d p.s (y - x) * r x) ∧
    Integrable (fun x => r x * ∫ y, rieszKernel p.d p.s (x - y) * D y) := by
  have hd : 2 ≤ p.d := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith [p.hs]
  have hgm : Measurable (rieszKernel p.d p.s) := S47.s47_kernel_measurable p.s
  have hkB : ∀ z : Euc p.d, z ≠ 0 → |rieszKernel p.d p.s z| ≤
      2 * ‖z‖ ^ (-movtr_sp p.s) + ‖z‖ + 1 := by
    intro z hz
    have h := movtr_gEps_abs_le (d := p.d) p.hs0 (ε := 0) le_rfl zero_le_one hz
    rw [movtr_gEps_zero p.d p.s] at h
    simpa using h
  set Fxy : Euc p.d × Euc p.d → ℝ :=
    fun z => r z.1 * (rieszKernel p.d p.s (z.1 - z.2) * D z.2) with hFxy
  have hM : Integrable (fun z : Euc p.d =>
      (2 * ‖z‖ ^ (-movtr_sp p.s) + ‖z‖ + 1) *
        Real.exp (-(E.c / 4) * ‖z‖ ^ 2)) :=
    movtr_majorant_integrable (by omega) p.hs0 hsd (c := E.c / 4)
      (by have := E.reference.hc; positivity)
  have hw : Integrable (fun y : Euc p.d => Real.exp (-(E.c / 2) * ‖y‖ ^ 2)) := by
    have h := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss p.d (b := E.c / 2)
      (by have := E.reference.hc; positivity)
    simpa [neg_mul] using h
  have hconv := Integrable.convolution_integrand
    (μ := (volume : Measure (Euc p.d))) (ν := volume)
    (ContinuousLinearMap.mul ℝ ℝ) hw hM
  have hFint : Integrable Fxy ((volume : Measure (Euc p.d)).prod volume) := by
    refine Integrable.mono' (hconv.const_mul (K1 * K2)) ?_ ?_
    · exact (hr.comp continuous_fst).aestronglyMeasurable.mul
        ((hgm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
          (hD.comp continuous_snd).aestronglyMeasurable)
    · have hne : ∀ᵐ z : Euc p.d × Euc p.d ∂((volume : Measure (Euc p.d)).prod volume),
        z.1 - z.2 ≠ 0 := by
        have h1 : ∀ᵐ z : Euc p.d ∂(volume : Measure (Euc p.d)), z ≠ 0 :=
          movtr_ae_ne_zero (d := p.d) (by omega)
        exact (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant
          (volume : Measure (Euc p.d)) (volume : Measure (Euc p.d))).ae h1
      filter_upwards [hne] with z hz
      simp only [hFxy, ContinuousLinearMap.mul_apply']
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have e1 := hrb z.1
      have e2 := hDb z.2
      have e3 := hkB _ hz
      have hexp : Real.exp (-E.c * ‖z.1‖ ^ 2) * Real.exp (-E.c * ‖z.2‖ ^ 2) ≤
          Real.exp (-(E.c / 4) * ‖z.1 - z.2‖ ^ 2) *
            Real.exp (-(E.c / 2) * ‖z.2‖ ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : ‖z.1 - z.2‖ ^ 2 ≤ 2 * ‖z.1‖ ^ 2 + 2 * ‖z.2‖ ^ 2 := by
          have h2 : ‖z.1 - z.2‖ ^ 2 ≤ (‖z.1‖ + ‖z.2‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le z.1 z.2) 2
          nlinarith [sq_nonneg (‖z.1‖ - ‖z.2‖)]
        have hc := E.reference.hc
        nlinarith [sq_nonneg ‖z.1‖, sq_nonneg ‖z.2‖]
      have hB0 : 0 ≤ 2 * ‖z.1 - z.2‖ ^ (-movtr_sp p.s) + ‖z.1 - z.2‖ + 1 := by
        have h := Real.rpow_nonneg (norm_nonneg (z.1 - z.2)) (-movtr_sp p.s)
        have := norm_nonneg (z.1 - z.2)
        linarith
      calc |r z.1| * (|rieszKernel p.d p.s (z.1 - z.2)| * |D z.2|)
          ≤ (K1 * Real.exp (-E.c * ‖z.1‖ ^ 2)) *
            ((2 * ‖z.1 - z.2‖ ^ (-movtr_sp p.s) + ‖z.1 - z.2‖ + 1) *
              (K2 * Real.exp (-E.c * ‖z.2‖ ^ 2))) :=
            mul_le_mul e1 (mul_le_mul e3 e2 (abs_nonneg _) hB0)
              (by positivity) (by positivity)
        _ = (K1 * K2) *
              ((2 * ‖z.1 - z.2‖ ^ (-movtr_sp p.s) + ‖z.1 - z.2‖ + 1) *
                (Real.exp (-E.c * ‖z.1‖ ^ 2) * Real.exp (-E.c * ‖z.2‖ ^ 2))) := by ring
        _ ≤ (K1 * K2) *
              ((2 * ‖z.1 - z.2‖ ^ (-movtr_sp p.s) + ‖z.1 - z.2‖ + 1) *
                (Real.exp (-(E.c / 4) * ‖z.1 - z.2‖ ^ 2) *
                  Real.exp (-(E.c / 2) * ‖z.2‖ ^ 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hB0)
              (by positivity)
        _ = K1 * K2 * (Real.exp (-(E.c / 2) * ‖z.2‖ ^ 2) *
              ((2 * ‖z.1 - z.2‖ ^ (-movtr_sp p.s) + ‖z.1 - z.2‖ + 1) *
                Real.exp (-(E.c / 4) * ‖z.1 - z.2‖ ^ 2))) := by ring
  have hswap := integral_integral_swap (f := fun x y => Fxy (x, y)) hFint
  have hg_even : ∀ x y : Euc p.d,
      rieszKernel p.d p.s (y - x) = rieszKernel p.d p.s (x - y) := by
    intro x y
    unfold rieszKernel
    rw [← norm_neg (y - x), neg_sub]
  have e1 : ∀ x, r x * ∫ y, rieszKernel p.d p.s (x - y) * D y =
      ∫ y, Fxy (x, y) := fun x => by rw [← integral_const_mul]
  have e2 : ∀ y, D y * ∫ x, rieszKernel p.d p.s (y - x) * r x =
      ∫ x, Fxy (x, y) := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFxy, hg_even x y]
    ring
  have hint_x : Integrable (fun x => r x *
      ∫ y, rieszKernel p.d p.s (x - y) * D y) :=
    (hFint.integral_prod_left).congr
      (Filter.Eventually.of_forall fun x => (e1 x).symm)
  refine ⟨?_, hint_x⟩
  simp_rw [e1, e2]
  exact hswap

/-- Weighted spatial divergence integration by parts at `ρ⁰`; this is a
Lebesgue-space identity and uses only the Gaussian envelope in `E.reference`. -/
theorem fp81s21_initialCancel_ibp_div
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (E : InitialSteinEnv R)
    {u : Euc p.d → ℝ} (hu : ContDiff ℝ 1 u) {Bu Du : ℝ}
    (hBu : ∀ y, |u y| ≤ Bu) (hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ Du)
    {v : Euc p.d → Euc p.d} (hv : ContDiff ℝ 1 v) {B1 B2 : ℝ}
    (hB1 : ∀ x, ‖v x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ v x‖ ≤ B2)
    {H : Euc p.d → ℝ} (hH : ContDiff ℝ 1 H) {MH DH : ℝ}
    (hHb : ∀ y, |H y| ≤ MH) (hHd : ∀ y, ‖fderiv ℝ H y‖ ≤ DH) :
    ∫ y, fp81s21_initialCancel_Dd R u v y * H y =
      -∫ y, fp81s21_initialCancel_rr R u y * fderiv ℝ H y (v y) := by
  have hd : 2 ≤ p.d := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    linarith [p.hs]
  obtain ⟨hr1, hr0, hr1'⟩ := fp81s21_initialCancel_r_bounds R E hu hBu hDu
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hMH0 : 0 ≤ MH := (abs_nonneg _).trans (hHb 0)
  have hDH0 : 0 ≤ DH := (norm_nonneg _).trans (hHd 0)
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
  have hC0 : 0 ≤ E.C := E.reference.C0
  have hCbase : 0 ≤ E.C * (Bu + Du + 1) := by positivity
  have hrd : Differentiable ℝ (fp81s21_initialCancel_rr R u) := hr1.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hHd' : Differentiable ℝ H := hH.differentiable one_ne_zero
  have hexp := fun y : Euc p.d => (Real.exp_pos (-E.c * ‖y‖ ^ 2)).le
  have hrc : Continuous (fderiv ℝ (fp81s21_initialCancel_rr R u)) := hr1.continuous_fderiv one_ne_zero
  have hvc : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hHc : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
  set e : Fin p.d → Euc p.d := fun b => EuclideanSpace.single b (1 : ℝ) with he
  have he1 : ∀ b, ‖e b‖ ≤ 1 := fun b => movtr_norm_single b
  set Fb : Fin p.d → Euc p.d → ℝ := fun b y =>
    fp81s21_initialCancel_rr R u y * v y b with hFb
  set Ph : Fin p.d → Euc p.d → ℝ := fun b y =>
    fp81s21_initialCancel_rr R u y * (fderiv ℝ v y (e b)) b +
      v y b * fderiv ℝ (fp81s21_initialCancel_rr R u) y (e b) with hPh
  have hFd : ∀ b y, HasFDerivAt (Fb b)
      (fp81s21_initialCancel_rr R u y •
        ((EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).comp (fderiv ℝ v y)) +
        v y b • fderiv ℝ (fp81s21_initialCancel_rr R u) y) y := by
    intro b y
    have h1 : HasFDerivAt (fun y => v y b)
        ((EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).comp (fderiv ℝ v y)) y :=
      (EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).hasFDerivAt.comp y (hvd y).hasFDerivAt
    exact (hrd y).hasFDerivAt.mul h1 |>.congr_fderiv (by ext z; simp)
  have hFd' : ∀ b y, fderiv ℝ (Fb b) y (e b) = Ph b y := by
    intro b y
    rw [(hFd b y).fderiv]
    simp [hPh]
  have hPhc : ∀ b, Continuous (Ph b) := fun b => by
    simp only [hPh]
    refine (hr1.continuous.mul ?_).add
      (((EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).continuous.comp hv.continuous).mul
        (hrc.clm_apply continuous_const))
    exact (EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).continuous.comp
      (hvc.clm_apply continuous_const)
  have hFbc : ∀ b, Continuous (Fb b) := fun b =>
    hr1.continuous.mul ((EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).continuous.comp hv.continuous)
  have hFbb : ∀ b y, |Fb b y| ≤ E.C * (Bu + Du + 1) * B1 *
      Real.exp (-E.c * ‖y‖ ^ 2) := by
    intro b y
    simp only [hFb]
    rw [abs_mul]
    calc |fp81s21_initialCancel_rr R u y| * |v y b| ≤
          (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) * B1 :=
          mul_le_mul (hr0 y) ((s45_abs_coord_le _ _).trans (hB1 y))
            (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hPhb : ∀ b y, |Ph b y| ≤ E.C * (Bu + Du + 1) * (B2 + B1) *
      Real.exp (-E.c * ‖y‖ ^ 2) := by
    intro b y
    simp only [hPh]
    have hC' : 0 ≤ E.C * (Bu + Du + 1) := by
      have hC := E.reference.C0
      have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
      have hDu0 : 0 ≤ Du := (norm_nonneg _).trans (hDu 0)
      positivity
    have e1 : |fp81s21_initialCancel_rr R u y * (fderiv ℝ v y (e b)) b| ≤
        (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) * B2 := by
      rw [abs_mul]
      refine mul_le_mul (hr0 y) ?_ (abs_nonneg _) (by have := hexp y; positivity)
      refine (s45_abs_coord_le _ _).trans ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖fderiv ℝ v y‖ * ‖e b‖ ≤ B2 * 1 :=
            mul_le_mul (hB2 y) (he1 b) (norm_nonneg _) hB20
        _ = B2 := mul_one _
    have e2 : |v y b * fderiv ℝ (fp81s21_initialCancel_rr R u) y (e b)| ≤
        B1 * (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) := by
      rw [abs_mul]
      refine mul_le_mul ((s45_abs_coord_le _ _).trans (hB1 y)) ?_ (abs_nonneg _) hB10
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖fderiv ℝ (fp81s21_initialCancel_rr R u) y‖ * ‖e b‖ ≤
            (E.C * (Bu + Du + 1) * Real.exp (-E.c * ‖y‖ ^ 2)) * 1 :=
            mul_le_mul (hr1' y) (he1 b) (norm_nonneg _) (by have := hexp y; positivity)
        _ = _ := mul_one _
    refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    ring
  have hint : ∀ b, Integrable (fun y => Ph b y * H y) := fun b => by
    refine fp81s21_initialCancel_gauss_int R E
      ((hPhc b).mul hH.continuous) (K :=
        E.C * (Bu + Du + 1) * (B2 + B1) * MH) (fun y => ?_)
    rw [abs_mul]
    calc |Ph b y| * |H y| ≤
          (E.C * (Bu + Du + 1) * (B2 + B1) * Real.exp (-E.c * ‖y‖ ^ 2)) * MH :=
          mul_le_mul (hPhb b y) (hHb y) (abs_nonneg _)
            (mul_nonneg (mul_nonneg hCbase (by positivity)) (hexp y))
      _ = _ := by ring
  have hcoord : ∀ b, ∫ y, Fb b y * fderiv ℝ H y (e b) =
      -∫ y, Ph b y * H y := by
    intro b
    have hI1 : Integrable (fun y => fderiv ℝ (Fb b) y (e b) * H y) :=
      (hint b).congr (Filter.Eventually.of_forall fun y => by simp only [hFd' b y])
    have hI2 : Integrable (fun y => Fb b y * fderiv ℝ H y (e b)) := by
      refine fp81s21_initialCancel_gauss_int R E
        ((hFbc b).mul (hHc.clm_apply continuous_const))
        (K := E.C * (Bu + Du + 1) * B1 * DH) (fun y => ?_)
      rw [abs_mul]
      have h : |fderiv ℝ H y (e b)| ≤ DH := by
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        calc ‖fderiv ℝ H y‖ * ‖e b‖ ≤ DH * 1 :=
              mul_le_mul (hHd y) (he1 b) (norm_nonneg _) hDH0
          _ = DH := mul_one _
      calc |Fb b y| * |fderiv ℝ H y (e b)| ≤
            (E.C * (Bu + Du + 1) * B1 * Real.exp (-E.c * ‖y‖ ^ 2)) * DH :=
            mul_le_mul (hFbb b y) h (abs_nonneg _)
              (mul_nonneg (mul_nonneg hCbase hB10) (hexp y))
        _ = _ := by ring
    have hI3 : Integrable (fun y => Fb b y * H y) := by
      refine fp81s21_initialCancel_gauss_int R E
        ((hFbc b).mul hH.continuous)
        (K := E.C * (Bu + Du + 1) * B1 * MH) (fun y => ?_)
      rw [abs_mul]
      calc |Fb b y| * |H y| ≤
            (E.C * (Bu + Du + 1) * B1 * Real.exp (-E.c * ‖y‖ ^ 2)) * MH :=
            mul_le_mul (hFbb b y) (hHb y) (abs_nonneg _)
              (by positivity)
        _ = _ := by ring
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Euc p.d))) (f := Fb b) (g := H) (v := e b)
      hI1 hI2 hI3 (fun x _ => ((hrd x).mul
        (((EuclideanSpace.proj b : Euc p.d →L[ℝ] ℝ).differentiableAt).comp x (hvd x))))
      (fun x _ => hHd' x)
    rw [h]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFd' b y]
  have hDsum : ∀ y, fp81s21_initialCancel_Dd R u v y = ∑ b, Ph b y := by
    intro y
    unfold fp81s21_initialCancel_Dd S45.s45_div
    simp only [hPh, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ b : Fin p.d, v y b * fderiv ℝ
        (fp81s21_initialCancel_rr R u) y (e b) =
        ⟪gradient (fp81s21_initialCancel_rr R u) y, v y⟫ := by
      rw [S99.s99_sum_basis (fderiv ℝ (fp81s21_initialCancel_rr R u) y) (v y),
        real_inner_comm]
      exact (HRS.MS.PoisKolm.kl_inner_gradient
        (fp81s21_initialCancel_rr R u) y (v y)).symm
    rw [h1]
    ring
  have hint2 : ∀ b, Integrable (fun y => Fb b y * fderiv ℝ H y (e b)) := by
    intro b
    refine fp81s21_initialCancel_gauss_int R E
      ((hFbc b).mul (hHc.clm_apply continuous_const))
      (K := E.C * (Bu + Du + 1) * B1 * DH) (fun y => ?_)
    rw [abs_mul]
    have h : |fderiv ℝ H y (e b)| ≤ DH := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖fderiv ℝ H y‖ * ‖e b‖ ≤ DH * 1 :=
            mul_le_mul (hHd y) (he1 b) (norm_nonneg _) hDH0
        _ = DH := mul_one _
    calc |Fb b y| * |fderiv ℝ H y (e b)| ≤
          (E.C * (Bu + Du + 1) * B1 * Real.exp (-E.c * ‖y‖ ^ 2)) * DH :=
          mul_le_mul (hFbb b y) h (abs_nonneg _)
            (mul_nonneg (mul_nonneg hCbase hB10) (hexp y))
      _ = _ := by ring
  have e1 : ∫ y, fp81s21_initialCancel_Dd R u v y * H y =
      ∑ b, ∫ y, Ph b y * H y := by
    have hfun : (fun y => fp81s21_initialCancel_Dd R u v y * H y) =
        fun y => ∑ b, Ph b y * H y := funext fun y => by
      rw [hDsum y, Finset.sum_mul]
    rw [hfun, integral_finsetSum _ (fun b _ => hint b)]
  have e2 : ∫ y, fp81s21_initialCancel_rr R u y *
      fderiv ℝ H y (v y) = ∑ b, ∫ y, Fb b y * fderiv ℝ H y (e b) := by
    have hfun : (fun y => fp81s21_initialCancel_rr R u y *
        fderiv ℝ H y (v y)) =
        fun y => ∑ b, Fb b y * fderiv ℝ H y (e b) := funext fun y => by
      simp only [hFb, mul_assoc, ← Finset.mul_sum]
      rw [S99.s99_sum_basis (fderiv ℝ H y) (v y)]
    rw [hfun, integral_finsetSum _ (fun b _ => hint2 b)]
  rw [e1, e2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by have h := hcoord b; linarith

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_initialCancel_gauss_int
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_LI_g
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_Dd_bd
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_swap
#print axioms HRS.Fp81.S21.fp81s21_initialCancel_ibp_div
