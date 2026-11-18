import HRS.MS.S111X2Aux30

/-!
# S11.1 X2, packet E07 (part 6): the Dirichlet energy of the orbit is differentiable (all times)
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

variable {d : ℕ}

theorem s111x2_inner_grad_coord (f g : Euc d → ℝ) (x : Euc d) :
    inner ℝ (gradient f x) (gradient g x) = ∑ i : Fin d, fderiv ℝ f x (EuclideanSpace.basisFun (Fin d) ℝ i) *
      fderiv ℝ g x (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner (gradient f x) (gradient g x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s111x2_inner_gradient, real_inner_comm, s111x2_inner_gradient]

section Dir

variable {s β : ℝ} {ρ : Euc d → ℝ} {M : ℝ} {C : WholeCoeff d}
variable {g : ℝ → Euc d → ℝ} {B1 B2 : ℝ} {φ : Euc d → ℝ} {A1 A2 : ℝ}

theorem s111x2_ftil_fderiv_apply (hg : C2Fam g B1 B2) (hφ : CbD φ A1 A2) (H r : ℝ) (y v : Euc d) :
    fderiv ℝ (s111x2_Ftil φ g H r) y v = fderiv ℝ φ y v + ∫ u in r..H, fderiv ℝ (g u) y v := by
  rw [s111x2_ftil_fderiv hg hφ H r y, add_apply]
  have hint : IntervalIntegrable (fun u => fderiv ℝ (g u) y) volume r H :=
    s111x2_intInt_param (fun u => fderiv ℝ (g u)) hg.c1 y r H
  exact congrArg _ (ContinuousLinearMap.intervalIntegral_apply (𝕜 := ℝ) hint v)

theorem s111x2_ftil_coord_deriv (hg : C2Fam g B1 B2) (hφ : CbD φ A1 A2) (H : ℝ) (x v : Euc d) (t : ℝ) :
    HasDerivAt (fun t => fderiv ℝ (s111x2_Ftil φ g H (H - t)) x v) (fderiv ℝ (g (H - t)) x v) t := by
  have hk : Continuous fun u => fderiv ℝ (g u) x v := (hg.c1.clm_apply continuous_const).comp
    (continuous_id.prodMk continuous_const)
  have h1 := intervalIntegral.integral_hasDerivAt_left (f := fun u => fderiv ℝ (g u) x v) (a := H - t) (b := H)
    (hk.intervalIntegrable _ _) hk.stronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have h2 : HasDerivAt (fun t : ℝ => H - t) (-1) t := by simpa using (hasDerivAt_id t).const_sub H
  have h3 := (h1.comp t h2).const_add (fderiv ℝ φ x v)
  have e : (fun t => fderiv ℝ (s111x2_Ftil φ g H (H - t)) x v) =
      fun t => fderiv ℝ φ x v + ((fun u => ∫ x_1 in u..H, fderiv ℝ (g x_1) x v) ∘ fun t => H - t) t :=
    funext fun t => by simp only [Function.comp_apply]; exact s111x2_ftil_fderiv_apply hg hφ H (H - t) x v
  rw [e]
  convert h3 using 1
  simp

theorem s111x2_ftil_grad_bound (hg : C2Fam g B1 B2) (hφ : CbD φ A1 A2) (H r : ℝ) (y : Euc d) :
    ‖fderiv ℝ (s111x2_Ftil φ g H r) y‖ ≤ A1 + B1 * |H - r| := by
  rw [s111x2_ftil_fderiv hg hφ H r y]
  refine (norm_add_le _ _).trans ?_
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := H) (C := B1)
    (f := fun u => fderiv ℝ (g u) y) (fun u _ => hg.b1 u y)
  have h2 : |H - r| = |r - H| := abs_sub_comm _ _
  nlinarith [hφ.d1 y, abs_nonneg (H - r)]

theorem s111x2_ftil_contDiff (hg : C2Fam g B1 B2) (hφ : CbD φ A1 A2) (H r : ℝ) :
    ContDiff ℝ 2 (s111x2_Ftil φ g H r) :=
  hφ.smooth.add (hg.contDiff r H)

theorem s111x2_dirichlet_deriv (T : TD d s β ρ M C) (hg : C2Fam g B1 B2) (hφ : CbD φ A1 A2) (H t : ℝ) :
    HasDerivAt (fun t => s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (s111x2_Ftil φ g H (H - t))
        (s111x2_Ftil φ g H (H - t)))
      (2 * s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (s111x2_Ftil φ g H (H - t)) (g (H - t))) t := by
  haveI := isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (hg.b1 0 0)
  have hA1 : 0 ≤ A1 := (norm_nonneg _).trans (hφ.d1 0)
  have hFe1 : ∀ t, ContDiff ℝ 1 (s111x2_Ftil φ g H (H - t)) := fun t =>
    (s111x2_ftil_contDiff hg hφ H (H - t)).of_le (by norm_num)
  have hgr : ∀ t, Continuous (gradient (s111x2_Ftil φ g H (H - t))) := fun t =>
    s111x2_gradient_continuous (hFe1 t)
  have hgg : ∀ t, Continuous (gradient (g (H - t))) := fun t =>
    s111x2_gradient_continuous ((hg.smooth _).of_le (by norm_num))
  set F : ℝ → Euc d → ℝ := fun t x => inner ℝ (gradient (s111x2_Ftil φ g H (H - t)) x)
    (gradient (s111x2_Ftil φ g H (H - t)) x) with hF
  set F' : ℝ → Euc d → ℝ := fun t x => 2 * inner ℝ (gradient (s111x2_Ftil φ g H (H - t)) x)
    (gradient (g (H - t)) x) with hF'
  have hgb : ∀ t' x, ‖gradient (s111x2_Ftil φ g H (H - t')) x‖ ≤ A1 + B1 * |t'| := fun t' x => by
    rw [s111x2_norm_gradient]
    have := s111x2_ftil_grad_bound hg hφ H (H - t') x
    simpa using this
  have hgb2 : ∀ u x, ‖gradient (g u) x‖ ≤ B1 := fun u x => by
    rw [s111x2_norm_gradient]; exact hg.b1 u x
  have hFint : Integrable (F t) μ := by
    refine (integrable_const ((A1 + B1 * |t|) ^ 2)).mono' ((hgr t).inner (hgr t)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [hF, real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hgb t x) 2
  have hbd : ∀ t' ∈ Metric.ball t 1, ∀ x, ‖F' t' x‖ ≤ 2 * (A1 + B1 * (|t| + 1)) * B1 := by
    intro t' ht' x
    have ht1 : |t'| ≤ |t| + 1 := by
      have := abs_sub_abs_le_abs_sub t' t
      rw [Metric.mem_ball, Real.dist_eq] at ht'
      linarith
    simp only [hF', Real.norm_eq_abs, abs_mul, abs_two]
    have h1 := abs_real_inner_le_norm (gradient (s111x2_Ftil φ g H (H - t')) x) (gradient (g (H - t')) x)
    have h2 : ‖gradient (s111x2_Ftil φ g H (H - t')) x‖ * ‖gradient (g (H - t')) x‖ ≤
        (A1 + B1 * (|t| + 1)) * B1 :=
      mul_le_mul ((hgb t' x).trans (by nlinarith)) (hgb2 _ x) (norm_nonneg _) (by positivity)
    nlinarith
  have hdiff : ∀ x, ∀ t' : ℝ, HasDerivAt (fun t'' => F t'' x) (F' t' x) t' := by
    intro x t'
    have hc : ∀ i : Fin d, HasDerivAt
        (fun t'' => fderiv ℝ (s111x2_Ftil φ g H (H - t'')) x (EuclideanSpace.basisFun (Fin d) ℝ i))
        (fderiv ℝ (g (H - t')) x (EuclideanSpace.basisFun (Fin d) ℝ i)) t' := fun i =>
      s111x2_ftil_coord_deriv hg hφ H x _ t'
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hc i).mul (hc i))
    have e1 : (fun t'' => F t'' x) = fun t'' => ∑ i : Fin d,
        fderiv ℝ (s111x2_Ftil φ g H (H - t'')) x (EuclideanSpace.basisFun (Fin d) ℝ i) *
          fderiv ℝ (s111x2_Ftil φ g H (H - t'')) x (EuclideanSpace.basisFun (Fin d) ℝ i) :=
      funext fun t'' => s111x2_inner_grad_coord _ _ x
    rw [e1]
    convert hsum using 1
    simp only [hF', s111x2_inner_grad_coord, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') (x₀ := t)
    (bound := fun _ => 2 * (A1 + B1 * (|t| + 1)) * B1) (s := Metric.ball t 1) (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun t' => ((hgr t').inner (hgr t')).aestronglyMeasurable) hFint
    (((hgr t).inner (hgg t)).const_mul 2).aestronglyMeasurable
    (Eventually.of_forall fun x t' ht' => hbd t' ht' x) (integrable_const _)
    (Eventually.of_forall fun x t' _ => hdiff x t')
  unfold s111x2_dirichlet
  convert hD using 1
  simp only [hF']
  rw [integral_const_mul]

end Dir

end HRS.MS.S111X2
