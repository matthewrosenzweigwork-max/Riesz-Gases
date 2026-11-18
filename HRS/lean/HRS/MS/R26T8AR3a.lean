import HRS.MS.R26T8AR2
import HRS.MS.R26T8AP22
import HRS.MS.R26T8AP22l
import HRS.MS.R26T8AP21

/-!
# S8.2 T8A R3a: the Newton potential of the exact leading source is `LI + S0`
`r26t8a_R3_src f x y = -(s/2) |x-y|^(-s) D²f(X)(û,û)`; `r26t8a_R3_raw_eq`: for `0 < |x-y| < 1`,
`rawNewton ν χ (src f) x y = LI ν (D²f(X)) (x-y) + S0 ν χ (D²f(X)) (x-y)` (P22 identity with its explicit smooth part `S0`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

def r26t8a_R3_src (f : Euc d → ℝ) : Euc d → Euc d → ℝ := fun x y =>
  (-(s82n_critS d / 2)) * ‖x - y‖ ^ (-s82n_critS d) *
    (fderiv ℝ (fderiv ℝ f) ((1 / 2 : ℝ) • (x + y))) (‖x - y‖⁻¹ • (x - y)) (‖x - y‖⁻¹ • (x - y))

theorem r26t8a_R3_symm {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X : Euc d) :
    ∀ u v : Euc d, fderiv ℝ (fderiv ℝ f) X u v = fderiv ℝ (fderiv ℝ f) X v u := fun u v =>
  (hf.contDiffAt.isSymmSndFDerivAt (by simp)) u v

theorem r26t8a_R3_raw_eq (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {x y : Euc d} (hxy : x ≠ y) (hx1 : ‖x - y‖ < 1) :
    rawNewton nu chi (r26t8a_R3_src f) x y =
      s82n_leadingInverse nu (fderiv ℝ (fderiv ℝ f) ((1 / 2 : ℝ) • (x + y))) (x - y) +
        r26t8a_p22_S0 nu chi (fderiv ℝ (fderiv ℝ f) ((1 / 2 : ℝ) • (x + y))) (x - y) := by
  haveI := r26t8a_nontrivial hd
  set B := fderiv ℝ (fderiv ℝ f) ((1 / 2 : ℝ) • (x + y)) with hB
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hcint := r26t8a_p22_Kint hd nu (r26t8a_p22_cfun_contDiff nu B hchi).continuous
    (r26t8a_p22_cfun_cs nu B hchi) (x - y)
  have hid := r26t8a_p22_identity hd nu hnu hchi B (r26t8a_R3_symm hf _) hz hx1 hcint
  unfold rawNewton
  rw [hchi.2.2.2.1 (x - y) hx1.le, one_mul]
  have e : ∫ w, newtonKernel d nu (x - y - w) * chi w * midPair (r26t8a_R3_src f) ((1 / 2 : ℝ) • (x + y)) w =
      ∫ w, newtonKernel d nu (x - y - w) * chi w *
        (-(s82n_critS d / 2) * ‖w‖ ^ (-s82n_critS d) * B (‖w‖⁻¹ • w) (‖w‖⁻¹ • w)) := by
    refine integral_congr_ae ?_
    filter_upwards [r26t8a_ae_ne_zero hd] with w hw
    have h1 : ((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • w) - ((1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • w) = w := by module
    have h2 : (1 / 2 : ℝ) • (((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • w) + ((1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • w)) =
        (1 / 2 : ℝ) • (x + y) := by module
    unfold midPair r26t8a_R3_src
    rw [h1, h2]
  rw [e, hid]
  unfold r26t8a_p22_S0
  rfl

end HRS.MS.R26T8A
