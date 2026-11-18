import HRS.MS.R26T8AP15l

/-!
# S8.2 T8A P15m: the `x`-local operator `Lop` of a pair function, in `dx` form
* `r26t8a_LxP_eq`: `Lop C Q(.,y) (x) = nu Σ_i dx_i dx_i Q + Σ_i α_i(x) dx_i Q` (slice `C²` at `x`; drift coordinates `α_i`);
* `r26t8a_LxP_conormal`: if `Q` is `Conormal (k+2) b M s A`, the right side is `Conormal k b (M+1) (s+2)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_dx_dx_eq (Q : Euc d → Euc d → ℝ) (x y : Euc d) (i : Fin d)
    (hQ : ContDiffAt ℝ 2 (fun w => Q w y) x) :
    r26t8a_dx i (r26t8a_dx i Q) x y =
      fderiv ℝ (fderiv ℝ (fun w => Q w y)) x (r26t8a_e d i) (r26t8a_e d i) := by
  set g : Euc d → ℝ := fun w => Q w y with hg
  have hfun : (fun x' => r26t8a_dx i Q x' y) = fun x' => (ContinuousLinearMap.apply ℝ ℝ (r26t8a_e d i)) (fderiv ℝ g x') := by
    funext x'
    rfl
  have hD : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  unfold r26t8a_dx
  show fderiv ℝ (fun x' => r26t8a_dx i Q x' y) x (r26t8a_e d i) = _
  rw [hfun]
  have h2 := (ContinuousLinearMap.apply ℝ ℝ (r26t8a_e d i)).hasFDerivAt.comp x hD.hasFDerivAt
  have h3 : fderiv ℝ (fun x' => (ContinuousLinearMap.apply ℝ ℝ (r26t8a_e d i)) (fderiv ℝ g x')) x =
      (ContinuousLinearMap.apply ℝ ℝ (r26t8a_e d i)).comp (fderiv ℝ (fderiv ℝ g) x) := h2.fderiv
  rw [h3]
  rfl

theorem r26t8a_LxP_eq (C : WholeCoeff d) (α : Fin d → Euc d → ℝ) (hb : ∀ i x, C.drift 0 x i = α i x)
    (Q : Euc d → Euc d → ℝ) (x y : Euc d) (hQ : ContDiffAt ℝ 2 (fun w => Q w y) x) :
    r26t8a_Lop C (fun w => Q w y) x =
      C.ν * ∑ i : Fin d, r26t8a_dx i (r26t8a_dx i Q) x y + ∑ i : Fin d, α i x * r26t8a_dx i Q x y := by
  unfold r26t8a_Lop
  rw [r26t8a_laplacian_basis, r26t8a_p15_inner_gradient, r26t8a_clm_expand]
  congr 1
  · congr 1
    exact (Finset.sum_congr rfl fun i _ => (r26t8a_dx_dx_eq Q x y i hQ).symm)
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb]
    rfl

end HRS.MS.R26T8A
