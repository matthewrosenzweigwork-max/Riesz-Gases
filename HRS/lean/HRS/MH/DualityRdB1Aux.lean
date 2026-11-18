import HRS.MH.DualityRdDefs
import HRS.Whole.Q09BAux3

/-!
# DualityRd packet B1 (auxiliary): analytic bounds for the mean-field generator on `ℝ^d`

Helpers for `mf_weak_integrable` (`DualityRdB1.lean`): gradient and Laplacian bounds of a `C_b²` test,
the kernel bound for `pairKernelRd`, and a uniform bound for `mfGen D ψ ρ` over a family of probability
densities with `ρ ≤ B` and a uniform second moment.  Helper names carry the prefix `db1_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Bounds for `C_b²` tests -/

theorem db1_iteratedFDeriv_bdd {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ} (hj : j ≤ k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf.2 j hj
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  exact (hB (Set.mem_range_self x)).trans (le_max_left _ _)

theorem db1_grad_norm_eq (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

theorem db1_grad_bound {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, ‖gradient ψ x‖ ≤ A := by
  obtain ⟨A, hA0, hA⟩ := db1_iteratedFDeriv_bdd hψ (j := 1) (by norm_num)
  refine ⟨A, hA0, fun x => ?_⟩
  have h := hA x
  rw [norm_iteratedFDeriv_one] at h
  rw [db1_grad_norm_eq]
  exact h

theorem db1_gradient_differentiable {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) (z : Euc d) :
    DifferentiableAt ℝ (gradient F) z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  have hgrad : gradient F = (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap ∘
      (fderiv ℝ F) := rfl
  rw [hgrad]
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.differentiableAt).comp z hd

theorem db1_fderiv_gradient_le {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) (z : Euc d) :
    ‖fderiv ℝ (gradient F) z‖ ≤ ‖fderiv ℝ (fderiv ℝ F) z‖ := by
  have hfd : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt
  have he' := ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap.hasFDerivAt).comp z hfd
  have hgrad : gradient F = (InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap ∘
      (fderiv ℝ F) := rfl
  have hg : fderiv ℝ (gradient F) z = ((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap).comp
      (fderiv ℝ (fderiv ℝ F) z) := by
    rw [hgrad, he'.fderiv]
  rw [hg]
  have hn : ‖(InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp)
  calc ‖((InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap).comp
        (fderiv ℝ (fderiv ℝ F) z)‖
      ≤ ‖(InnerProductSpace.toDual ℝ (Euc d)).symm.toContinuousLinearMap‖ *
          ‖fderiv ℝ (fderiv ℝ F) z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ (fderiv ℝ F) z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg (fderiv ℝ (fderiv ℝ F) z))
    _ = ‖fderiv ℝ (fderiv ℝ F) z‖ := one_mul _

theorem db1_grad_lip {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Euc d, ‖gradient ψ x - gradient ψ y‖ ≤ L * ‖x - y‖ := by
  obtain ⟨L, hL0, hL⟩ := db1_iteratedFDeriv_bdd hψ (j := 2) (by norm_num)
  refine ⟨L, hL0, fun x y => ?_⟩
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (gradient ψ) z‖ ≤ L := by
    intro z _
    refine (db1_fderiv_gradient_le hψ.1 z).trans ?_
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ψ) (x := z) (n := 1)
    have h2 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := z) (fderiv ℝ ψ)
    rw [← h2, h1]
    exact hL z
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => db1_gradient_differentiable hψ.1 z) hb convex_univ (Set.mem_univ x) (Set.mem_univ y)
  rw [norm_sub_rev (gradient ψ x), norm_sub_rev x y]
  exact h

theorem db1_gradient_continuous {F : Euc d → ℝ} (hF : ContDiff ℝ 2 F) : Continuous (gradient F) :=
  continuous_iff_continuousAt.2 fun z => (db1_gradient_differentiable hF z).continuousAt

theorem db1_laplacian_bound {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |Laplacian.laplacian ψ x| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := db1_iteratedFDeriv_bdd hψ (j := 2) (by norm_num)
  refine ⟨(Module.finrank ℝ (Euc d) : ℝ) * B, by positivity, fun x => ?_⟩
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have key : ∀ i, ‖iteratedFDeriv ℝ 2 ψ x
      ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]‖ ≤ B := by
    intro i
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hb : ∏ j : Fin 2, ‖(![(stdOrthonormalBasis ℝ (Euc d)) i,
        (stdOrthonormalBasis ℝ (Euc d)) i] : Fin 2 → Euc d) j‖ = 1 := by
      simp [Fin.prod_univ_two, OrthonormalBasis.norm_eq_one]
    rw [hb, mul_one]
    exact hB x
  calc |∑ i, iteratedFDeriv ℝ 2 ψ x
        ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]|
      = ‖∑ i, iteratedFDeriv ℝ 2 ψ x
        ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ 2 ψ x
        ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (Euc d)), B := Finset.sum_le_sum fun i _ => key i
    _ = (Module.finrank ℝ (Euc d) : ℝ) * B := by
        simp [Finset.sum_const, nsmul_eq_mul]

theorem db1_laplacian_continuous {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (Laplacian.laplacian ψ) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  have hc : Continuous (iteratedFDeriv ℝ 2 ψ) := hψ.continuous_iteratedFDeriv (m := 2) le_rfl
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i]).continuous).comp hc

/-! ### The interaction kernel -/

theorem db1_matVec_bound (M : Matrix (Fin d) (Fin d) ℝ) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ v : Euc d, ‖Torus.matVec M v‖ ≤ CM * ‖v‖ := by
  refine ⟨‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖, norm_nonneg _, fun v => ?_⟩
  exact (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm v

/-- The singular part `|z|^{-s} 1_{|z| < 1}` of the kernel bound. -/
def db1G (s : ℝ) : Euc d → ℝ := Set.indicator (Metric.ball (0 : Euc d) 1) (fun z => ‖z‖ ^ (-s))

theorem db1G_nonneg (s : ℝ) (z : Euc d) : 0 ≤ db1G s z := by
  unfold db1G
  refine Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z

theorem db1G_integrable {s : ℝ} (hd : 1 ≤ d) (hsd : s < d) : Integrable (db1G (d := d) s) := by
  unfold db1G
  rw [integrable_indicator_iff measurableSet_ball]
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) ?_ (C := 1) (α := s) (r := 1) ?_ ?_ ?_
  · rw [finrank_euclideanSpace_fin]; exact hd
  · rw [finrank_euclideanSpace_fin]; exact_mod_cast hsd
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  · exact (Measurable.aestronglyMeasurable (by fun_prop))

/-- Uniform kernel bound: `|pairKernelRd D ψ x y| ≤ K (|x-y|^{-s} 1_{|x-y|<1} + 1)` for `ψ ∈ C_b²`. -/
theorem db1_pK_bound (D : WholeDyn d) (hs0 : 0 ≤ D.s) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ x y : Euc d, |pairKernelRd D ψ x y| ≤ Kc * (db1G D.s (x - y) + 1) := by
  obtain ⟨A, hA0, hA⟩ := db1_grad_bound hψ
  obtain ⟨L, hL0, hL⟩ := db1_grad_lip hψ
  obtain ⟨CM, hCM0, hCM⟩ := db1_matVec_bound D.M
  refine ⟨CM * |movtr_sigma D.s| * (L + 2 * A), by positivity, fun x y => ?_⟩
  unfold pairKernelRd
  split_ifs with hxy
  · rw [abs_zero]
    have : 0 ≤ db1G D.s (x - y) + 1 := by linarith [db1G_nonneg D.s (x - y)]
    exact mul_nonneg (by positivity) this
  · have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hzpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hz
    have hk : ‖rieszKernelGrad d D.s (x - y)‖ = |movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1) := by
      rw [movtr_rieszKernelGrad_norm D.s hs0 hz]
      have hr : 0 ≤ ‖x - y‖ ^ (-D.s - 1) := Real.rpow_nonneg (norm_nonneg _) _
      have h1 : |movtr_sigma D.s * ‖x - y‖ ^ (-D.s - 1)| = movtr_sigma D.s * ‖x - y‖ ^ (-D.s - 1) := by
        rw [← movtr_rieszKernelGrad_norm D.s hs0 hz]
        exact abs_of_nonneg (norm_nonneg _)
      rw [abs_mul, abs_of_nonneg hr] at h1
      exact h1.symm
    have hinner : |inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))|
        ≤ ‖gradient ψ x - gradient ψ y‖ * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← hk]
      exact hCM _
    have hdiff : ‖gradient ψ x - gradient ψ y‖ ≤ L * ‖x - y‖ := hL x y
    have hdiff2 : ‖gradient ψ x - gradient ψ y‖ ≤ 2 * A := by
      refine (norm_sub_le _ _).trans ?_
      linarith [hA x, hA y]
    have hC0 : 0 ≤ CM * |movtr_sigma D.s| := by positivity
    by_cases h1 : ‖x - y‖ < 1
    · -- near field: the bound is `L |z|^{-s}`
      have hind : db1G D.s (x - y) = ‖x - y‖ ^ (-D.s) := by
        unfold db1G
        rw [Set.indicator_of_mem (by simpa using h1)]
      have hpow : ‖x - y‖ * ‖x - y‖ ^ (-D.s - 1) = ‖x - y‖ ^ (-D.s) := by
        rw [mul_comm, ← Real.rpow_add_one hzpos.ne']
        congr 1
        ring
      have hg : 0 ≤ ‖x - y‖ ^ (-D.s) := Real.rpow_nonneg (norm_nonneg _) _
      calc |inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))|
          ≤ ‖gradient ψ x - gradient ψ y‖ * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) := hinner
        _ ≤ (L * ‖x - y‖) * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) :=
            mul_le_mul_of_nonneg_right hdiff (by positivity)
        _ = (CM * |movtr_sigma D.s| * L) * (‖x - y‖ ^ (-D.s)) := by rw [← hpow]; ring
        _ ≤ (CM * |movtr_sigma D.s| * (L + 2 * A)) * (db1G D.s (x - y) + 1) := by
            rw [hind]
            have hLA : L ≤ L + 2 * A := by linarith
            have hX : 0 ≤ CM * |movtr_sigma D.s| * ‖x - y‖ ^ (-D.s) := by positivity
            nlinarith [mul_le_mul_of_nonneg_right hLA hg, mul_nonneg hC0 hg]
    · -- far field: the bound is `2 A |z|^{-s-1} ≤ 2 A`
      have hind : db1G D.s (x - y) = 0 := by
        unfold db1G
        rw [Set.indicator_of_notMem (by simpa using h1)]
      have hr1 : ‖x - y‖ ^ (-D.s - 1) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (not_lt.1 h1) (by linarith)
      calc |inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y)))|
          ≤ ‖gradient ψ x - gradient ψ y‖ * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) := hinner
        _ ≤ (2 * A) * (CM * (|movtr_sigma D.s| * ‖x - y‖ ^ (-D.s - 1))) :=
            mul_le_mul_of_nonneg_right hdiff2 (by positivity)
        _ ≤ (2 * A) * (CM * (|movtr_sigma D.s| * 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr1 (abs_nonneg _)) (by positivity)
        _ = (CM * |movtr_sigma D.s| * (2 * A)) * (db1G D.s (x - y) + 1) := by rw [hind]; ring
        _ ≤ (CM * |movtr_sigma D.s| * (L + 2 * A)) * (db1G D.s (x - y) + 1) := by
            rw [hind]
            have : CM * |movtr_sigma D.s| * (2 * A) ≤ CM * |movtr_sigma D.s| * (L + 2 * A) :=
              mul_le_mul_of_nonneg_left (by linarith) hC0
            linarith

/-! ### The mean-field generator on a density -/

theorem db1_prob_integrable {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  norm_num at this

theorem db1_measurable_G (s : ℝ) : Measurable (db1G (d := d) s) := by
  unfold db1G
  exact Measurable.indicator (measurable_norm.pow_const _) measurableSet_ball

theorem db1_rho_kernel_le {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B)
    (s : ℝ) (x : Euc d) (hBint : Integrable (db1G (d := d) s)) :
    ∫ y, ρ y * db1G s (x - y) ≤ B * ∫ z, db1G (d := d) s z := by
  have hGt : Integrable (fun y => db1G (d := d) s (x - y)) := hBint.comp_sub_left x
  have hBG : Integrable (fun y => B * db1G (d := d) s (x - y)) := hGt.const_mul B
  have hmeas : AEStronglyMeasurable (fun y => ρ y * db1G (d := d) s (x - y)) volume :=
    (hρ.measurable.mul ((db1_measurable_G s).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  have hi : Integrable (fun y => ρ y * db1G (d := d) s (x - y)) := by
    refine hBG.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg y) (db1G_nonneg s _))]
    exact mul_le_mul_of_nonneg_right (hB y) (db1G_nonneg s _)
  calc ∫ y, ρ y * db1G s (x - y) ≤ ∫ y, B * db1G (d := d) s (x - y) :=
        integral_mono hi hBG (fun y => mul_le_mul_of_nonneg_right (hB y) (db1G_nonneg s _))
    _ = B * ∫ z, db1G (d := d) s z := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (db1G (d := d) s) volume x

theorem db1_matVec_continuous (M : Matrix (Fin d) (Fin d) ℝ) : Continuous (Torus.matVec M : Euc d → Euc d) :=
  (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).continuous

theorem db1_pK_measurable {D : WholeDyn d} {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Measurable (fun p : Euc d × Euc d => pairKernelRd D ψ p.1 p.2) := by
  unfold pairKernelRd
  have hdiag : MeasurableSet {p : Euc d × Euc d | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  refine Measurable.ite hdiag measurable_const ?_
  have hg : Measurable (gradient ψ) := (db1_gradient_continuous hψ).measurable
  exact ((hg.comp measurable_fst).sub (hg.comp measurable_snd)).inner
    ((db1_matVec_continuous D.M).measurable.comp
      ((movtr_rieszKernelGrad_measurable D.s).comp (measurable_fst.sub measurable_snd)))

/-- The pointwise bound of the interaction integrand: `|∫ ρ(y) pairKernelRd x y dy| ≤ K (B I + 1)`. -/
theorem db1_J_bound {D : WholeDyn d} (hd : 1 ≤ d) (hsd : D.s < d) {Kc : ℝ} (hKc0 : 0 ≤ Kc)
    {ψ : Euc d → ℝ} (hK : ∀ x y : Euc d, |pairKernelRd D ψ x y| ≤ Kc * (db1G D.s (x - y) + 1))
    {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B) (x : Euc d) :
    |∫ y, ρ y * pairKernelRd D ψ x y| ≤ Kc * (B * (∫ z, db1G (d := d) D.s z) + 1) := by
  have hBint := db1G_integrable (d := d) hd hsd
  have hGt : Integrable (fun y => db1G (d := d) D.s (x - y)) := hBint.comp_sub_left x
  have hρint := db1_prob_integrable hρ
  have hmeasG : Measurable (fun y => db1G (d := d) D.s (x - y)) :=
    (db1_measurable_G D.s).comp (measurable_const.sub measurable_id)
  have hi1 : Integrable (fun y => ρ y * db1G (d := d) D.s (x - y)) := by
    have hBG : Integrable (fun y => B * db1G (d := d) D.s (x - y)) := hGt.const_mul B
    refine hBG.mono' (hρ.measurable.mul hmeasG).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg y) (db1G_nonneg D.s _))]
    exact mul_le_mul_of_nonneg_right (hB y) (db1G_nonneg D.s _)
  have hgi : Integrable (fun y => ρ y * (Kc * (db1G (d := d) D.s (x - y) + 1))) := by
    have e : (fun y => ρ y * (Kc * (db1G (d := d) D.s (x - y) + 1)))
        = fun y => Kc * (ρ y * db1G (d := d) D.s (x - y)) + Kc * ρ y := by
      funext y; ring
    rw [e]
    exact (hi1.const_mul Kc).add (hρint.const_mul Kc)
  have hpt : ∀ y, ‖ρ y * pairKernelRd D ψ x y‖ ≤ ρ y * (Kc * (db1G (d := d) D.s (x - y) + 1)) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
    exact mul_le_mul_of_nonneg_left (hK x y) (hρ.nonneg y)
  have hkey : ∫ y, ρ y * (Kc * (db1G (d := d) D.s (x - y) + 1))
      = Kc * (∫ y, ρ y * db1G (d := d) D.s (x - y)) + Kc := by
    have e : (fun y => ρ y * (Kc * (db1G (d := d) D.s (x - y) + 1)))
        = fun y => Kc * (ρ y * db1G (d := d) D.s (x - y)) + Kc * ρ y := by
      funext y; ring
    rw [e, integral_add (hi1.const_mul Kc) (hρint.const_mul Kc), integral_const_mul,
      integral_const_mul, hρ.integral_one, mul_one]
  have hrk := db1_rho_kernel_le hρ hB D.s x hBint
  rw [← Real.norm_eq_abs]
  calc ‖∫ y, ρ y * pairKernelRd D ψ x y‖
      ≤ ∫ y, ρ y * (Kc * (db1G (d := d) D.s (x - y) + 1)) :=
        norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hpt)
    _ = Kc * (∫ y, ρ y * db1G (d := d) D.s (x - y)) + Kc := hkey
    _ ≤ Kc * (B * (∫ z, db1G (d := d) D.s z)) + Kc :=
        add_le_add (mul_le_mul_of_nonneg_left hrk hKc0) le_rfl
    _ = Kc * (B * (∫ z, db1G (d := d) D.s z) + 1) := by ring

/-- The generator `mfGen` on a density, as a Lebesgue integral with the kernel `pairKernelRd`. -/
theorem db1_mfGen_eq (D : WholeDyn d) {ψ ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) :
    mfGen D ψ ρ = (∫ x, ρ x * (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)))
      + (1 / 2 : ℝ) * ∫ x, ρ x * ∫ y, ρ y * pairKernelRd D ψ x y := by
  have h1 := Q09A.pair_withDensityReal hρ
    (fun x => D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))
  have h2 : ∀ x : Euc d, ∫ y, (if x = y then (0 : ℝ) else
      inner ℝ (gradient ψ x - gradient ψ y) (Torus.matVec D.M (rieszKernelGrad d D.s (x - y))))
      ∂(Whole.withDensityReal ρ) = ∫ y, ρ y * pairKernelRd D ψ x y :=
    fun x => Q09A.pair_withDensityReal hρ (fun y => pairKernelRd D ψ x y)
  have h3 : ∫ x, (∫ y, ρ y * pairKernelRd D ψ x y) ∂(Whole.withDensityReal ρ)
      = ∫ x, ρ x * ∫ y, ρ y * pairKernelRd D ψ x y :=
    Q09A.pair_withDensityReal hρ (fun x => ∫ y, ρ y * pairKernelRd D ψ x y)
  unfold mfGen interactionPairingW
  rw [h1]
  simp only [h2]
  rw [h3]

/-- Uniform bound of the generator over a family of probability densities with `ρ ≤ B` and a
uniform second moment `∫ ρ |x|² ≤ M2`. -/
theorem db1_mfGen_bound {ΛV G0 : ℝ} (D : WholeDyn d) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hV : VHypRd 2 ΛV G0 D.V) {ψ : Euc d → ℝ} (hψ : MemCb 2 ψ) (B M2 : ℝ) (hB0 : 0 ≤ B) :
    ∃ K : ℝ, ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ B) →
      Integrable (fun x => ρ x * ‖x‖ ^ 2) → ∫ x, ρ x * ‖x‖ ^ 2 ≤ M2 → |mfGen D ψ ρ| ≤ K := by
  obtain ⟨A, hA0, hA⟩ := db1_grad_bound hψ
  obtain ⟨C, hC0, hC⟩ := db1_laplacian_bound hψ
  obtain ⟨Kc, hKc0, hK⟩ := db1_pK_bound D hs0 hψ
  have hG0 : 0 ≤ G0 := (norm_nonneg _).trans hV.2.2
  have hgV : ∀ x, ‖gradient D.V x‖ ≤ G0 + ΛV * ‖x‖ := fun x => Q09B.q09b_gradV_bound le_rfl hV x
  set c0 : ℝ := |D.invβ| * C + A * G0 with hc0
  set c1 : ℝ := A * |ΛV| with hc1
  have hc1_0 : 0 ≤ c1 := mul_nonneg hA0 (abs_nonneg _)
  have hgT : ∀ x, |D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x)|
      ≤ c0 + c1 * ‖x‖ := by
    intro x
    refine (abs_sub _ _).trans ?_
    have h1 : |D.invβ * Laplacian.laplacian ψ x| ≤ |D.invβ| * C := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)
    have hnn : 0 ≤ G0 + ΛV * ‖x‖ := (norm_nonneg _).trans (hgV x)
    have h2 : |inner ℝ (gradient D.V x) (gradient ψ x)| ≤ (G0 + ΛV * ‖x‖) * A :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hgV x) (hA x) (norm_nonneg _) hnn)
    have h3 : (G0 + ΛV * ‖x‖) * A ≤ A * G0 + A * |ΛV| * ‖x‖ := by
      have : 0 ≤ A * ‖x‖ * (|ΛV| - ΛV) :=
        mul_nonneg (mul_nonneg hA0 (norm_nonneg _)) (sub_nonneg.2 (le_abs_self ΛV))
      nlinarith
    rw [hc0, hc1]
    linarith
  have hpoint : ∀ x : Euc d, c0 + c1 * ‖x‖ ≤ (c0 + c1 / 2) + (c1 / 2) * ‖x‖ ^ 2 := by
    intro x
    nlinarith [sq_nonneg (‖x‖ - 1), hc1_0]
  refine ⟨(c0 + c1 / 2) + (c1 / 2) * M2 + (1 / 2 : ℝ) * (Kc * (B * (∫ z, db1G (d := d) D.s z) + 1)),
    fun ρ hρ hB hsq hM2 => ?_⟩
  have hρint := db1_prob_integrable hρ
  have hmaj : Integrable (fun x => ρ x * ((c0 + c1 / 2) + (c1 / 2) * ‖x‖ ^ 2)) := by
    have e : (fun x => ρ x * ((c0 + c1 / 2) + (c1 / 2) * ‖x‖ ^ 2))
        = fun x => (c0 + c1 / 2) * ρ x + (c1 / 2) * (ρ x * ‖x‖ ^ 2) := by
      funext x; ring
    rw [e]
    exact (hρint.const_mul _).add (hsq.const_mul _)
  have hI1 : |∫ x, ρ x * (D.invβ * Laplacian.laplacian ψ x - inner ℝ (gradient D.V x) (gradient ψ x))|
      ≤ ∫ x, ρ x * ((c0 + c1 / 2) + (c1 / 2) * ‖x‖ ^ 2) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
    exact mul_le_mul_of_nonneg_left ((hgT x).trans (hpoint x)) (hρ.nonneg x)
  have hI2 : ∫ x, ρ x * ((c0 + c1 / 2) + (c1 / 2) * ‖x‖ ^ 2)
      = (c0 + c1 / 2) + (c1 / 2) * ∫ x, ρ x * ‖x‖ ^ 2 := by
    have e : (fun x => ρ x * ((c0 + c1 / 2) + (c1 / 2) * ‖x‖ ^ 2))
        = fun x => (c0 + c1 / 2) * ρ x + (c1 / 2) * (ρ x * ‖x‖ ^ 2) := by
      funext x; ring
    rw [e, integral_add (hρint.const_mul _) (hsq.const_mul _), integral_const_mul, integral_const_mul,
      hρ.integral_one, mul_one]
  have hJ := db1_J_bound (D := D) hd hsd hKc0 hK hρ hB
  have hI3 : |∫ x, ρ x * ∫ y, ρ y * pairKernelRd D ψ x y|
      ≤ Kc * (B * (∫ z, db1G (d := d) D.s z) + 1) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, ρ x * ∫ y, ρ y * pairKernelRd D ψ x y‖
        ≤ ∫ x, ρ x * (Kc * (B * (∫ z, db1G (d := d) D.s z) + 1)) := by
          refine norm_integral_le_of_norm_le (hρint.mul_const _) (Filter.Eventually.of_forall fun x => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
          exact mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hJ x) (hρ.nonneg x)
      _ = Kc * (B * (∫ z, db1G (d := d) D.s z) + 1) := by
          rw [integral_mul_const, hρ.integral_one, one_mul]
  rw [db1_mfGen_eq D hρ]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hM : (c0 + c1 / 2) + (c1 / 2) * ∫ x, ρ x * ‖x‖ ^ 2 ≤ (c0 + c1 / 2) + (c1 / 2) * M2 :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_left hM2 (by linarith [hc1_0] : (0 : ℝ) ≤ c1 / 2))
  have hA1 := hI1.trans ((le_of_eq hI2).trans hM)
  have hB3 : (1 / 2 : ℝ) * |∫ x, ρ x * ∫ y, ρ y * pairKernelRd D ψ x y|
      ≤ (1 / 2 : ℝ) * (Kc * (B * (∫ z, db1G (d := d) D.s z) + 1)) :=
    mul_le_mul_of_nonneg_left hI3 (by norm_num)
  linarith

end HRS.MH.DualityRd
