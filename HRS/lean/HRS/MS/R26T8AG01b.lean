import HRS.MS.R26T8AG01a

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper b): derivatives of a composition `ψ ∘ h`

For `ψ : ℝ → ℝ` smooth and `h : E → ℝ` smooth on a finite-dimensional normed space:
`‖∂(ψ∘h) x‖ ≤ |ψ'(h x)| ‖∂h x‖` and
`‖∂²(ψ∘h) x‖ ≤ |ψ'(h x)| ‖∂²h x‖ + |ψ''(h x)| ‖∂h x‖²`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_g01b_smul_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ℝ) (b : F) :
    ‖a • b‖ ≤ |a| * ‖b‖ := by
  rw [norm_smul, Real.norm_eq_abs]

theorem r26t8a_g01b_fderiv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    (x : E) : ‖fderiv ℝ (fun y => ψ (h y)) x‖ ≤ |deriv ψ (h x)| * ‖fderiv ℝ h x‖ := by
  have hψd : HasDerivAt ψ (deriv ψ (h x)) (h x) :=
    ((hψ.differentiable (by simp)) (h x)).hasDerivAt
  have hhd : HasFDerivAt h (fderiv ℝ h x) x :=
    ((hh.differentiable (by simp)) x).hasFDerivAt
  have hf : HasFDerivAt (fun y => ψ (h y)) (deriv ψ (h x) • fderiv ℝ h x) x :=
    hψd.comp_hasFDerivAt x hhd
  rw [hf.fderiv, norm_smul, Real.norm_eq_abs]

theorem r26t8a_g01b_iter2 {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    (x : E) : ‖iteratedFDeriv ℝ 2 (fun y => ψ (h y)) x‖ ≤
      |deriv ψ (h x)| * ‖iteratedFDeriv ℝ 2 h x‖ + |deriv (deriv ψ) (h x)| * ‖fderiv ℝ h x‖ ^ 2 := by
  have hψ1 : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
  have hψd : HasDerivAt ψ (deriv ψ (h x)) (h x) :=
    ((hψ.differentiable (by simp)) (h x)).hasDerivAt
  have hψ1d : HasDerivAt (deriv ψ) (deriv (deriv ψ) (h x)) (h x) :=
    ((hψ1.differentiable (by simp)) (h x)).hasDerivAt
  have hhd : HasFDerivAt h (fderiv ℝ h x) x :=
    ((hh.differentiable (by simp)) x).hasFDerivAt
  have hDh : Differentiable ℝ (fderiv ℝ h) := (hh.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have hDhd : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) x) x := (hDh x).hasFDerivAt
  have hc : HasFDerivAt (fun y => deriv ψ (h y)) (deriv (deriv ψ) (h x) • fderiv ℝ h x) x :=
    hψ1d.comp_hasFDerivAt x hhd
  have hf : fderiv ℝ (fun y => ψ (h y)) = fun y => deriv ψ (h y) • fderiv ℝ h y := by
    funext y
    exact (((hψ.differentiable (by simp)) (h y)).hasDerivAt.comp_hasFDerivAt y
      ((hh.differentiable (by simp)) y).hasFDerivAt).fderiv
  have hder : HasFDerivAt (fun y => deriv ψ (h y) • fderiv ℝ h y)
      (deriv ψ (h x) • fderiv ℝ (fderiv ℝ h) x +
        (deriv (deriv ψ) (h x) • fderiv ℝ h x).smulRight (fderiv ℝ h x)) x :=
    hc.smul hDhd
  have h2 : ‖iteratedFDeriv ℝ 2 (fun y => ψ (h y)) x‖ = ‖fderiv ℝ (fderiv ℝ (fun y => ψ (h y))) x‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ (fun y => ψ (h y))) (x := x)]
    rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y => ψ (h y)) (x := x) (n := 1)]
  have h3 : ‖iteratedFDeriv ℝ 2 h x‖ = ‖fderiv ℝ (fderiv ℝ h) x‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ h) (x := x)]
    rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := h) (x := x) (n := 1)]
  rw [h2, hf, hder.fderiv, h3]
  refine (norm_add_le (deriv ψ (h x) • fderiv ℝ (fderiv ℝ h) x)
    ((deriv (deriv ψ) (h x) • fderiv ℝ h x).smulRight (fderiv ℝ h x))).trans ?_
  have hA := r26t8a_g01b_smul_norm (deriv ψ (h x)) (fderiv ℝ (fderiv ℝ h) x)
  have hB : ‖(deriv (deriv ψ) (h x) • fderiv ℝ h x).smulRight (fderiv ℝ h x)‖ ≤
      |deriv (deriv ψ) (h x)| * ‖fderiv ℝ h x‖ ^ 2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply, sq]
    have hc := r26t8a_g01b_smul_norm (deriv (deriv ψ) (h x)) (fderiv ℝ h x)
    calc ‖deriv (deriv ψ) (h x) • fderiv ℝ h x‖ * ‖fderiv ℝ h x‖
        ≤ |deriv (deriv ψ) (h x)| * ‖fderiv ℝ h x‖ * ‖fderiv ℝ h x‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ = |deriv (deriv ψ) (h x)| * (‖fderiv ℝ h x‖ * ‖fderiv ℝ h x‖) := by ring
  linarith

end HRS.MS.R26T8A

end
