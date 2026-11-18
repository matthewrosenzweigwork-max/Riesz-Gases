import HRS.MS.R26T8AF07e
import HRS.MS.R26T8AF07d

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07f): additivity of the local generator `localP`

For smooth `p, q`: `localP (p + q) = localP p + localP q` pointwise (Laplacian, Euler and gradient are additive).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07f_D_add (i : Fin d) (p q : Euc d → ℝ) (hp : Differentiable ℝ p)
    (hq : Differentiable ℝ q) :
    r26t8a_l3_D i (fun y => p y + q y) = fun y => r26t8a_l3_D i p y + r26t8a_l3_D i q y := by
  funext y
  unfold r26t8a_l3_D
  rw [show (fun z => p z + q z) = p + q from rfl, fderiv_add (hp y) (hq y)]
  rfl

theorem r26t8a_f07f_lap_add (p q : Euc d → ℝ) (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q)
    (x : Euc d) :
    Laplacian.laplacian (fun y => p y + q y) x = Laplacian.laplacian p x + Laplacian.laplacian q x := by
  rw [r26t8a_f07c_lap _ (hp.add hq) x, r26t8a_f07c_lap p hp x, r26t8a_f07c_lap q hq x,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hDp : Differentiable ℝ (r26t8a_l3_D i p) :=
    ((r26t8a_l3_contDiff_D i p hp).differentiable (by simp))
  have hDq : Differentiable ℝ (r26t8a_l3_D i q) :=
    ((r26t8a_l3_contDiff_D i q hq).differentiable (by simp))
  have hp1 : Differentiable ℝ p := hp.differentiable (by simp)
  have hq1 : Differentiable ℝ q := hq.differentiable (by simp)
  rw [r26t8a_f07f_D_add i p q hp1 hq1, r26t8a_f07f_D_add i _ _ hDp hDq]

theorem r26t8a_f07f_grad_add (p q : Euc d → ℝ) (hp : Differentiable ℝ p) (hq : Differentiable ℝ q)
    (x : Euc d) :
    gradient (fun y => p y + q y) x = gradient p x + gradient q x := by
  unfold gradient
  rw [show (fun y => p y + q y) = p + q from rfl, fderiv_add (hp x) (hq x), map_add]

theorem r26t8a_f07f_localP_add (a beta : ℝ) (rho p q : Euc d → ℝ) (hp : ContDiff ℝ ∞ p)
    (hq : ContDiff ℝ ∞ q) (x : Euc d) :
    r26t8a_localP a beta rho (fun y => p y + q y) x =
      r26t8a_localP a beta rho p x + r26t8a_localP a beta rho q x := by
  have hp1 : Differentiable ℝ p := hp.differentiable (by simp)
  have hq1 : Differentiable ℝ q := hq.differentiable (by simp)
  unfold r26t8a_localP
  rw [r26t8a_f07f_lap_add p q hp hq x, r26t8a_f07f_grad_add p q hp1 hq1 x, inner_add_right,
    show (fun y => p y + q y) = p + q from rfl, fderiv_add (hp1 x) (hq1 x),
    ContinuousLinearMap.add_apply]
  ring

end HRS.MS.R26T8A

end
