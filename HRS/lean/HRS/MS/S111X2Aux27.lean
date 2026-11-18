import HRS.MS.S111X2Aux26
import HRS.MS.S111X2Aux19

/-!
# S11.1 X2, packet E07 (part 2): the generator in terms of `fderiv`, and its commutation with time integrals
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.S111X1 (EnData KData Nnl)

variable {d : ℕ}

theorem s111x2_lap_eq (f : Euc d → ℝ) (x : Euc d) :
    Laplacian.laplacian f x = ∑ i : Fin d, fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp [iteratedFDeriv_two_apply]

theorem s111x2_inner_gradient (f : Euc d → ℝ) (y v : Euc d) :
    inner ℝ (gradient f y) v = fderiv ℝ f y v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

section Core

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}

theorem s111x2_gen_fderiv (T : TD d s β ρ M C) {f : Euc d → ℝ} {B1 B2 : ℝ} (H : CbD f B1 B2) (x : Euc d) :
    generatorW C 0 f x = β⁻¹ * Laplacian.laplacian f x + fderiv ℝ f x (C.drift 0 x) +
      ∫ y, ρ y * fderiv ℝ f y (rieszKernelGrad d s (x - y)) := by
  have hg1 : ∀ y, ‖gradient f y‖ ≤ B1 := fun y => by rw [s111x2_norm_gradient]; exact H.d1 y
  rw [HRS.MS.S111X1.gen_formula T.en H.smooth hg1 0 x, real_inner_comm, s111x2_inner_gradient]
  simp_rw [s111x2_inner_gradient]

end Core

section Param

variable {g : ℝ → Euc d → ℝ} {B1 B2 : ℝ}

theorem s111x2_param_fderiv_apply (hg : C2Fam g B1 B2) (a b : ℝ) (x v : Euc d) :
    fderiv ℝ (fun y => ∫ u in a..b, g u y) x v = ∫ u in a..b, fderiv ℝ (g u) x v := by
  rw [hg.fderiv_eq]
  have hint : IntervalIntegrable (fun u => fderiv ℝ (g u) x) volume a b :=
    s111x2_intInt_param (fun u => fderiv ℝ (g u)) hg.c1 x a b
  exact ((ContinuousLinearMap.apply ℝ ℝ v).intervalIntegral_comp_comm hint).symm

theorem s111x2_param_fderiv₂_apply (hg : C2Fam g B1 B2) (a b : ℝ) (x v w : Euc d) :
    fderiv ℝ (fderiv ℝ (fun y => ∫ u in a..b, g u y)) x v w = ∫ u in a..b, fderiv ℝ (fderiv ℝ (g u)) x v w := by
  rw [hg.fderiv₂_eq]
  have hint : IntervalIntegrable (fun u => fderiv ℝ (fderiv ℝ (g u)) x) volume a b :=
    s111x2_intInt_param (fun u => fderiv ℝ (fderiv ℝ (g u))) hg.c2 x a b
  have h1 := ContinuousLinearMap.intervalIntegral_apply (𝕜 := ℝ) hint v
  have hint2 : IntervalIntegrable (fun u => fderiv ℝ (fderiv ℝ (g u)) x v) volume a b :=
    s111x2_intInt_param (fun u y => fderiv ℝ (fderiv ℝ (g u)) y v)
      (hg.c2.clm_apply continuous_const) x a b
  have h2 := ContinuousLinearMap.intervalIntegral_apply (𝕜 := ℝ) hint2 w
  rw [h1, h2]

theorem s111x2_lap_u_continuous (hg : C2Fam g B1 B2) (x : Euc d) :
    Continuous fun u => Laplacian.laplacian (g u) x := by
  have : (fun u => Laplacian.laplacian (g u) x) = fun u => ∑ i : Fin d, fderiv ℝ (fderiv ℝ (g u)) x
      (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) :=
    funext fun u => s111x2_lap_eq (g u) x
  rw [this]
  exact continuous_finsetSum _ fun i _ =>
    ((hg.c2.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const).clm_apply continuous_const

theorem s111x2_param_lap (hg : C2Fam g B1 B2) (a b : ℝ) (x : Euc d) :
    Laplacian.laplacian (fun y => ∫ u in a..b, g u y) x = ∫ u in a..b, Laplacian.laplacian (g u) x := by
  rw [s111x2_lap_eq]
  simp_rw [s111x2_param_fderiv₂_apply hg, s111x2_lap_eq (g _)]
  rw [intervalIntegral.integral_finsetSum]
  intro i _
  exact (((hg.c2.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const).clm_apply
    continuous_const).intervalIntegrable _ _

end Param

section NL

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} {g : ℝ → Euc d → ℝ} {B1 B2 : ℝ}

/-- Joint integrability of the nonlocal integrand on `Ioc a b × ℝ^d`. -/
theorem s111x2_nl_integrable (T : TD d s β ρ M C) (hg : C2Fam g B1 B2) (a b : ℝ) (x : Euc d) :
    Integrable (fun p : ℝ × Euc d => ρ p.2 * fderiv ℝ (g p.1) p.2 (rieszKernelGrad d s (x - p.2)))
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hK := HRS.MS.S111X1.kG_weighted T.en.K.hd T.en.K.hs0 T.en.K.hs1 T.en.K.meas T.en.K.nonneg
    T.en.K.int T.en.K.bdd x
  have hgrad : Continuous fun p : ℝ × Euc d => gradient (g p.1) p.2 :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp hg.c1
  have hkm : Measurable fun p : ℝ × Euc d => rieszKernelGrad d s (x - p.2) :=
    (HRS.MS.S111X1.kG_measurable s).comp (measurable_const.sub measurable_snd)
  have hmeas : Measurable (fun p : ℝ × Euc d => ρ p.2 * fderiv ℝ (g p.1) p.2 (rieszKernelGrad d s (x - p.2))) := by
    have e : (fun p : ℝ × Euc d => ρ p.2 * fderiv ℝ (g p.1) p.2 (rieszKernelGrad d s (x - p.2))) =
        fun p => ρ p.2 * inner ℝ (gradient (g p.1) p.2) (rieszKernelGrad d s (x - p.2)) :=
      funext fun p => by rw [s111x2_inner_gradient]
    rw [e]
    exact (T.en.K.meas.comp measurable_snd).mul (Measurable.inner hgrad.measurable hkm)
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hg.b1 0 0)
  have hbd : Integrable (fun p : ℝ × Euc d => (1 : ℝ) * (B1 * (ρ p.2 * ‖rieszKernelGrad d s (x - p.2)‖)))
      ((volume.restrict (Ioc a b)).prod volume) :=
    (integrable_const (1 : ℝ)).mul_prod (hK.1.const_mul B1)
  refine hbd.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (T.en.K.nonneg p.2), one_mul]
  have h1 : |fderiv ℝ (g p.1) p.2 (rieszKernelGrad d s (x - p.2))| ≤ B1 * ‖rieszKernelGrad d s (x - p.2)‖ := by
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ (g p.1) p.2).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hg.b1 _ _) (norm_nonneg _))
  calc ρ p.2 * |fderiv ℝ (g p.1) p.2 (rieszKernelGrad d s (x - p.2))|
      ≤ ρ p.2 * (B1 * ‖rieszKernelGrad d s (x - p.2)‖) := by gcongr; exact T.en.K.nonneg _
    _ = B1 * (ρ p.2 * ‖rieszKernelGrad d s (x - p.2)‖) := by ring

theorem s111x2_nl_swap (T : TD d s β ρ M C) (hg : C2Fam g B1 B2) {a b : ℝ} (hab : a ≤ b) (x : Euc d) :
    ∫ y, (∫ u in a..b, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y))) =
      ∫ u in a..b, ∫ y, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y)) ∧
    Integrable (fun y => ∫ u in a..b, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y))) ∧
    IntervalIntegrable (fun u => ∫ y, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y))) volume a b := by
  have hI := s111x2_nl_integrable T hg a b x
  refine ⟨?_, ?_, ?_⟩
  · have h2 : Integrable (Function.uncurry fun u y => ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y)))
        ((volume.restrict (Set.uIoc a b)).prod volume) := by
      rw [Set.uIoc_of_le hab]; exact hI
    exact (intervalIntegral_integral_swap h2).symm
  · simp_rw [intervalIntegral.integral_of_le hab]
    exact hI.integral_prod_right
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hI.integral_prod_left

end NL

section GenInt

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d} {g : ℝ → Euc d → ℝ} {B1 B2 : ℝ}

theorem s111x2_cbD_add_param (hg : C2Fam g B1 B2) {φ : Euc d → ℝ} {A1 A2 : ℝ} (hφ : CbD φ A1 A2)
    {a b : ℝ} (hab : a ≤ b) :
    CbD (fun y => φ y + ∫ u in a..b, g u y) (A1 + (b - a) * B1) (A2 + (b - a) * B2) := by
  have hΦ := hg.contDiff a b
  have hfd : fderiv ℝ (fun y => φ y + ∫ u in a..b, g u y) =
      fun y => fderiv ℝ φ y + ∫ u in a..b, fderiv ℝ (g u) y := by
    funext y
    rw [fderiv_fun_add (hφ.smooth.differentiable (by norm_num) y)
      ((hg.hasFDerivAt a b y).differentiableAt), (hg.hasFDerivAt a b y).fderiv]
  have hn1 : ∀ y, ‖∫ u in a..b, fderiv ℝ (g u) y‖ ≤ B1 * (b - a) := fun y => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := B1)
      (f := fun u => fderiv ℝ (g u) y) (fun u _ => hg.b1 u y)
    rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
  have hn2 : ∀ y, ‖∫ u in a..b, fderiv ℝ (fderiv ℝ (g u)) y‖ ≤ B2 * (b - a) := fun y => by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := B2)
      (f := fun u => fderiv ℝ (fderiv ℝ (g u)) y) (fun u _ => hg.b2 u y)
    rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
  refine ⟨hφ.smooth.add hΦ, fun y => ?_, fun y => ?_⟩
  · rw [hfd]
    refine (norm_add_le _ _).trans ?_
    have := hn1 y
    nlinarith [hφ.d1 y]
  · have hdd : fderiv ℝ (fderiv ℝ (fun y => φ y + ∫ u in a..b, g u y)) y =
        fderiv ℝ (fderiv ℝ φ) y + ∫ u in a..b, fderiv ℝ (fderiv ℝ (g u)) y := by
      rw [hfd, fderiv_fun_add ((hφ.smooth.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y)
        ((hg.hasFDerivAt₂ a b y).differentiableAt), (hg.hasFDerivAt₂ a b y).fderiv]
    rw [hdd]
    refine (norm_add_le _ _).trans ?_
    have := hn2 y
    nlinarith [hφ.d2 y]

theorem s111x2_gen_integral (T : TD d s β ρ M C) (hg : C2Fam g B1 B2) {φ : Euc d → ℝ} {A1 A2 : ℝ}
    (hφ : CbD φ A1 A2) {a b : ℝ} (hab : a ≤ b) (x : Euc d) :
    generatorW C 0 (fun y => φ y + ∫ u in a..b, g u y) x =
      generatorW C 0 φ x + ∫ u in a..b, generatorW C 0 (g u) x ∧
    IntervalIntegrable (fun u => generatorW C 0 (g u) x) volume a b := by
  have hgu : ∀ u, CbD (g u) B1 B2 := fun u => ⟨hg.smooth u, hg.b1 u, hg.b2 u⟩
  have hf := s111x2_cbD_add_param hg hφ hab
  have hΦ := hg.contDiff a b
  obtain ⟨hswap, hNint, hNii⟩ := s111x2_nl_swap T hg hab x
  have hKint := (HRS.MS.S111X1.kG_weighted T.en.K.hd T.en.K.hs0 T.en.K.hs1 T.en.K.meas T.en.K.nonneg
    T.en.K.int T.en.K.bdd x).1
  have hlapi : IntervalIntegrable (fun u => Laplacian.laplacian (g u) x) volume a b :=
    (s111x2_lap_u_continuous hg x).intervalIntegrable _ _
  have hdrift : Continuous fun u => fderiv ℝ (g u) x (C.drift 0 x) :=
    (hg.c1.comp (continuous_id.prodMk continuous_const)).clm_apply continuous_const
  have hdi : IntervalIntegrable (fun u => fderiv ℝ (g u) x (C.drift 0 x)) volume a b :=
    hdrift.intervalIntegrable _ _
  have hGu : ∀ u, generatorW C 0 (g u) x = β⁻¹ * Laplacian.laplacian (g u) x + fderiv ℝ (g u) x (C.drift 0 x) +
      ∫ y, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y)) := fun u => s111x2_gen_fderiv T (hgu u) x
  have hii : IntervalIntegrable (fun u => generatorW C 0 (g u) x) volume a b := by
    simp_rw [hGu]
    exact ((hlapi.const_mul _).add hdi).add hNii
  refine ⟨?_, hii⟩
  rw [s111x2_gen_fderiv T hf x, s111x2_gen_fderiv T hφ x]
  simp_rw [hGu]
  rw [intervalIntegral.integral_add ((hlapi.const_mul _).add hdi) hNii,
    intervalIntegral.integral_add (hlapi.const_mul _) hdi, intervalIntegral.integral_const_mul]
  -- the three pieces
  have hL : Laplacian.laplacian (fun y => φ y + ∫ u in a..b, g u y) x =
      Laplacian.laplacian φ x + ∫ u in a..b, Laplacian.laplacian (g u) x := by
    rw [← s111x2_param_lap hg a b x]
    exact (hφ.smooth.contDiffAt).laplacian_add hΦ.contDiffAt
  have hD : fderiv ℝ (fun y => φ y + ∫ u in a..b, g u y) x (C.drift 0 x) =
      fderiv ℝ φ x (C.drift 0 x) + ∫ u in a..b, fderiv ℝ (g u) x (C.drift 0 x) := by
    rw [fderiv_fun_add (hφ.smooth.differentiable (by norm_num) x) ((hg.hasFDerivAt a b x).differentiableAt),
      add_apply, s111x2_param_fderiv_apply hg]
  have hN : ∫ y, ρ y * fderiv ℝ (fun y => φ y + ∫ u in a..b, g u y) y (rieszKernelGrad d s (x - y)) =
      (∫ y, ρ y * fderiv ℝ φ y (rieszKernelGrad d s (x - y))) +
        ∫ u in a..b, ∫ y, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y)) := by
    have hpt : ∀ y, ρ y * fderiv ℝ (fun y => φ y + ∫ u in a..b, g u y) y (rieszKernelGrad d s (x - y)) =
        ρ y * fderiv ℝ φ y (rieszKernelGrad d s (x - y)) +
          ∫ u in a..b, ρ y * fderiv ℝ (g u) y (rieszKernelGrad d s (x - y)) := fun y => by
      rw [fderiv_fun_add (hφ.smooth.differentiable (by norm_num) y) ((hg.hasFDerivAt a b y).differentiableAt),
        add_apply, s111x2_param_fderiv_apply hg, mul_add, intervalIntegral.integral_const_mul]
    have hP : Integrable (fun y => ρ y * fderiv ℝ φ y (rieszKernelGrad d s (x - y))) := by
      have hA1 : 0 ≤ A1 := (norm_nonneg _).trans (hφ.d1 0)
      refine (hKint.const_mul A1).mono' ?_ (Eventually.of_forall fun y => ?_)
      · have hgrad : Continuous (gradient φ) := s111x2_gradient_continuous (hφ.smooth.of_le (by norm_num))
        have e : (fun y => ρ y * fderiv ℝ φ y (rieszKernelGrad d s (x - y))) =
            fun y => ρ y * inner ℝ (gradient φ y) (rieszKernelGrad d s (x - y)) :=
          funext fun y => by rw [s111x2_inner_gradient]
        rw [e]
        exact (T.en.K.meas.mul (Measurable.inner hgrad.measurable
          ((HRS.MS.S111X1.kG_measurable s).comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (T.en.K.nonneg y)]
        have h1 : |fderiv ℝ φ y (rieszKernelGrad d s (x - y))| ≤ A1 * ‖rieszKernelGrad d s (x - y)‖ := by
          rw [← Real.norm_eq_abs]
          exact ((fderiv ℝ φ y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hφ.d1 _) (norm_nonneg _))
        calc ρ y * |fderiv ℝ φ y (rieszKernelGrad d s (x - y))|
            ≤ ρ y * (A1 * ‖rieszKernelGrad d s (x - y)‖) := by gcongr; exact T.en.K.nonneg _
          _ = A1 * (ρ y * ‖rieszKernelGrad d s (x - y)‖) := by ring
    simp_rw [hpt]
    rw [integral_add hP hNint, hswap]
  rw [hL, hD, hN]
  ring

end GenInt

end HRS.MS.S111X2
