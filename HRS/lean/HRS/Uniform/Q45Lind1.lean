import HRS.Prob.MartingaleCLT

/-!
# Q45: a Lindeberg bound with a general Hessian-pairing seminorm and an `ℱ₀`-measurable shift

Helpers for Proposition 3.21 (`smooth_path_comparison`).  Namespace `HRS.Uniform.Q45`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The Hessian pairing `∑ᵢⱼ ∇²u(x)(eᵢ,eⱼ) Qᵢⱼ`. -/
def hessPair (u : (ℝ^p) → ℝ) (x : ℝ^p) (Q : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∑ i, ∑ j, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] * Q i j

lemma gs_abs_le {h : (ℝ^p) → ℝ} {B : ℝ} (hB : ∀ x, |h x| ≤ B) (Q : Matrix (Fin p) (Fin p) ℝ)
    (x : ℝ^p) : |gaussSmooth h Q x| ≤ B := by
  unfold gaussSmooth
  have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : ℝ^p) Q) (C := B)
    (f := fun y => h (x + y)) (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB _)
  simpa using this

lemma gs_fderiv_le {h : (ℝ^p) → ℝ} (hh : ContDiff ℝ 2 h) {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) {G1 : ℝ} (hG : ∀ x, ‖fderiv ℝ h x‖ ≤ G1)
    (Q : Matrix (Fin p) (Fin p) ℝ) (x : ℝ^p) : ‖fderiv ℝ (gaussSmooth h Q) x‖ ≤ G1 := by
  obtain ⟨h1, -, -⟩ := gaussSmooth_derivs Q h hh H hH
  rw [(h1 x).fderiv]
  have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian (0 : ℝ^p) Q) (C := G1)
    (f := fun z => fderiv ℝ h (x + z)) (ae_of_all _ fun z => hG _)
  simpa using this

lemma gs_hess_apply {h : (ℝ^p) → ℝ} (hh : ContDiff ℝ 2 h) {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) (Q : Matrix (Fin p) (Fin p) ℝ) (x a b : ℝ^p) :
    iteratedFDeriv ℝ 2 (gaussSmooth h Q) x ![a, b] =
      ∫ z, iteratedFDeriv ℝ 2 h (x + z) ![a, b] ∂(multivariateGaussian (0 : ℝ^p) Q) := by
  set γ := multivariateGaussian (0 : ℝ^p) Q with hγ
  obtain ⟨h1, h2, -⟩ := gaussSmooth_derivs Q h hh H hH
  have hfd : fderiv ℝ (gaussSmooth h Q) = fun x => ∫ z, fderiv ℝ h (x + z) ∂γ :=
    funext fun x => (h1 x).fderiv
  have hfd2 : fderiv ℝ (fderiv ℝ (gaussSmooth h Q)) x =
      ∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂γ := by
    rw [hfd]; exact (h2 x).fderiv
  have hc : Continuous (fderiv ℝ (fderiv ℝ h)) :=
    (hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hG := integrable_shift_of_bdd (V := (ℝ^p) →L[ℝ] (ℝ^p) →L[ℝ] ℝ) γ (fderiv ℝ (fderiv ℝ h)) hc H
    (norm_hess_le hH) x
  have hψ : Integrable (fun z => fderiv ℝ (fderiv ℝ h) (x + z) a) γ := by
    refine integrable_shift_of_bdd (V := (ℝ^p) →L[ℝ] ℝ) γ (fun w => fderiv ℝ (fderiv ℝ h) w a)
      (by fun_prop) (H * ‖a‖) (fun w => ?_) x
    exact ((fderiv ℝ (fderiv ℝ h) w).le_opNorm a).trans (by gcongr; exact norm_hess_le hH w)
  have e2 : (∫ z, fderiv ℝ (fderiv ℝ h) (x + z) ∂γ) a b =
      ∫ z, fderiv ℝ (fderiv ℝ h) (x + z) a b ∂γ := by
    rw [ContinuousLinearMap.integral_apply hG a, ContinuousLinearMap.integral_apply hψ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hfd2, e2]

lemma gs_hessPair_le {h : (ℝ^p) → ℝ} (hh : ContDiff ℝ 2 h) {H : ℝ}
    (hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H) {Hp : ℝ} {ν : Matrix (Fin p) (Fin p) ℝ → ℝ}
    (hR : ∀ x (Q' : Matrix (Fin p) (Fin p) ℝ), |hessPair h x Q'| ≤ Hp * ν Q')
    (Q : Matrix (Fin p) (Fin p) ℝ) (x : ℝ^p) (Q' : Matrix (Fin p) (Fin p) ℝ) :
    |hessPair (gaussSmooth h Q) x Q'| ≤ Hp * ν Q' := by
  set γ := multivariateGaussian (0 : ℝ^p) Q with hγ
  have hint : ∀ i j, Integrable (fun z => iteratedFDeriv ℝ 2 h (x + z)
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] * Q' i j) γ := by
    intro i j
    refine Integrable.mul_const ?_ _
    refine integrable_shift_of_bdd (V := ℝ) γ (fun w => iteratedFDeriv ℝ 2 h w
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ^p) ℝ
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]).continuous.comp
        (hh.continuous_iteratedFDeriv le_rfl)) H (fun w => ?_) x
    have := (iteratedFDeriv ℝ 2 h w).le_opNorm ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.norm_single,
      norm_one, mul_one] at this
    exact this.trans (hH w)
  have e : hessPair (gaussSmooth h Q) x Q' =
      ∫ z, hessPair h (x + z) Q' ∂γ := by
    unfold hessPair
    simp_rw [gs_hess_apply hh hH Q x]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  rw [e, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := γ) (C := Hp * ν Q')
    (f := fun z => hessPair h (x + z) Q') (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hR _ _)
  simpa using this

end HRS.Uniform.Q45
