import HRS.MS.SA12NN2C
import HRS.MS.SA12Z3NearN5B

/-!
# S.A.12 N2 (SA12N), part D: linearity/continuity of `hessRiesz`; the case `s < d - 1`

`a Hv - H(a v) = H[(a(x) - a(·)) v](x) = ∫ K(x-y)(a(x)-a(y)) v(y) dy`, the integrand being bounded by
`C ‖a‖_{C²} ‖x-y‖^{-s-1} |v(y)|` (an `L¹` kernel for `s < d-1`), then `sa12n_young_pow`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a HRS.MS.UniqN2b

variable {d : ℕ}

/-- `g * v` is `C²` for `v ∈ C²_c`. -/
theorem sa12n_conv_contDiff {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ContDiff ℝ 2 (HRS.Whole.convFun (rieszKernel d s) v) := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hfun' : HRS.Whole.convFun (rieszKernel d s) v =
      rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] v := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * v (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  rw [hfun']
  exact hvc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hv

theorem sa12n_hess_apply (s : ℝ) (i j : Fin d) (v : Euc d → ℝ) (x : Euc d) :
    hessRiesz d s i j v x = iteratedFDeriv ℝ 2 (HRS.Whole.convFun (rieszKernel d s) v) x
      (fun l => EuclideanSpace.single (if l = 0 then i else j) (1 : ℝ)) := rfl

theorem sa12n_hess_continuous {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) : Continuous (hessRiesz d s i j v) := by
  have hcd := sa12n_conv_contDiff hs0 hsd hv hvc
  have hc := hcd.continuous_iteratedFDeriv (m := 2) le_rfl
  have : hessRiesz d s i j v = fun x => iteratedFDeriv ℝ 2 (HRS.Whole.convFun (rieszKernel d s) v) x
      (fun l => EuclideanSpace.single (if l = 0 then i else j) (1 : ℝ)) := funext fun x => rfl
  rw [this]
  exact hc.eval_const _

/-- Linearity of `hessRiesz` on `C²_c`. -/
theorem sa12n_hess_lin {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {f1 f2 : Euc d → ℝ}
    (h1 : ContDiff ℝ 2 f1) (h1c : HasCompactSupport f1) (h2 : ContDiff ℝ 2 f2)
    (h2c : HasCompactSupport f2) (c : ℝ) (x : Euc d) :
    hessRiesz d s i j (fun y => c * f1 y - f2 y) x =
      c * hessRiesz d s i j f1 x - hessRiesz d s i j f2 x := by
  have hc1 := sa12n_conv_contDiff hs0 hsd h1 h1c
  have hc2 := sa12n_conv_contDiff hs0 hsd h2 h2c
  have hI : ∀ f : Euc d → ℝ, ContDiff ℝ 2 f → HasCompactSupport f → ∀ y,
      Integrable (fun z => rieszKernel d s (y - z) * f z) volume := fun f hf hfc y =>
    n2b_conv_integrable hs0 hsd hf.continuous hfc y
  have hfun : HRS.Whole.convFun (rieszKernel d s) (fun y => c * f1 y - f2 y) =
      c • HRS.Whole.convFun (rieszKernel d s) f1 - HRS.Whole.convFun (rieszKernel d s) f2 := by
    funext y
    simp only [HRS.Whole.convFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul, ← integral_sub ((hI f1 h1 h1c y).const_mul c) (hI f2 h2 h2c y)]
    congr 1; funext z; ring
  have e1 : iteratedFDeriv ℝ 2 (c • HRS.Whole.convFun (rieszKernel d s) f1 -
      HRS.Whole.convFun (rieszKernel d s) f2) x =
      iteratedFDeriv ℝ 2 (c • HRS.Whole.convFun (rieszKernel d s) f1) x -
        iteratedFDeriv ℝ 2 (HRS.Whole.convFun (rieszKernel d s) f2) x :=
    iteratedFDeriv_sub_apply (f := c • HRS.Whole.convFun (rieszKernel d s) f1)
      (g := HRS.Whole.convFun (rieszKernel d s) f2) (hc1.const_smul c).contDiffAt hc2.contDiffAt
  have e2 : iteratedFDeriv ℝ 2 (c • HRS.Whole.convFun (rieszKernel d s) f1) x =
      c • iteratedFDeriv ℝ 2 (HRS.Whole.convFun (rieszKernel d s) f1) x :=
    iteratedFDeriv_const_smul_apply hc1.contDiffAt
  rw [sa12n_hess_apply, sa12n_hess_apply, sa12n_hess_apply, hfun, e1, e2]
  simp

end HRS.MH.AdjointRd.Phase2SA12Near
