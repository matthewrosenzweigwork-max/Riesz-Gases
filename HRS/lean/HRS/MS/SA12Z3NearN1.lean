import HRS.MS.SA12NearDefs
import HRS.MS.UniqN1cA

/-!
# S.A.12 N1 (SA12Z3): `hess_local_finite`

The finite-regularity local Hessian bound for `hessRiesz`. For `v ∈ C²_b` supported in a ball,
`v` is `C²` with compact support, and `hessRiesz d s i j v = ∂_i (g * ∂_j v)` (the literal second
iterated derivative of the convolution, by `n1b_qq_bil`); the bound is `n1c_hess_local`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- The literal Hessian entry equals `∂_i (g * ∂_j v)` for `v ∈ C²_c`. -/
theorem sa12z3_hess_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (x : Euc d) :
    hessRiesz d s i j v x =
      D1 i (HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v) x := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hfun : (fun x' => ∫ y, rieszKernel d s (x' - y) * v y) =
      HRS.Whole.convFun (rieszKernel d s) v := rfl
  have hfun' : HRS.Whole.convFun (rieszKernel d s) v =
      rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] v := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * v (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  have hcd : ContDiff ℝ 2 (HRS.Whole.convFun (rieszKernel d s) v) := by
    rw [hfun']
    exact hvc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hv
  have hD : ∀ y, D1 j (HRS.Whole.convFun (rieszKernel d s) v) y =
      HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v y := fun y =>
    convFun_D1 hK (hv.of_le (by norm_num)) hvc j y
  unfold hessRiesz
  rw [hfun, iteratedFDeriv_two_apply]
  simp only [ite_true, show ¬ ((1 : Fin 2) = 0) from by decide, ite_false]
  have h1 := HRS.MS.UniqN1b.n1b_qq_bil hcd (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ)) x
  have h2 : (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) v) z
      (EuclideanSpace.single j (1 : ℝ))) = HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v :=
    funext fun y => hD y
  rw [h2] at h1
  rw [← h1]
  rfl

/-- A function with `MemCb 2` supported in a closed ball is `C²` with compact support. -/
theorem sa12z3_memCb_cc {c : Euc d} {ρ : ℝ} {v : Euc d → ℝ} (hv : MemCb 2 v)
    (hsupp : Function.support v ⊆ Metric.closedBall c ρ) :
    ContDiff ℝ 2 v ∧ HasCompactSupport v := by
  refine ⟨by simpa using hv.1, ?_⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c ρ) hsupp

/-- **N1.** `hess_local_finite`. -/
theorem hess_local_finite (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hs2 : s ≤ (d : ℝ)-2) :
    ∃ C C₀ : ℝ, 0 < C ∧ 0 ≤ C₀ ∧ ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ →
      ∀ (c : Euc d) (v : Euc d → ℝ), MemCb 2 v →
      Function.support v ⊆ Metric.closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((Metric.closedBall c' r').indicator (hessRiesz d s i j v)) 2 volume ≤
          ENNReal.ofReal (C*ρ^C₀)*eLpNorm v 2 volume := by
  have hsd : s < d := by linarith
  obtain ⟨C₀, C, h⟩ := HRS.MS.UniqN1c.n1c_hess_local hd hs0 hs2
  refine ⟨|C| + 1, max C₀ 0, by positivity, le_max_right _ _, fun i j ρ hρ c v hv hsupp c' r' hr' => ?_⟩
  obtain ⟨hv2, hvc⟩ := sa12z3_memCb_cc hv hsupp
  have hfun : hessRiesz d s i j v = fun y => D1 i (HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v) y :=
    funext fun x => sa12z3_hess_eq hs0 hsd i j hv2 hvc x
  rw [hfun]
  refine (h j i ρ hρ c v hv2 hvc hsupp c' r' hr').trans ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have h1 : ρ ^ C₀ ≤ ρ ^ (max C₀ 0) := Real.rpow_le_rpow_of_exponent_le hρ (le_max_left _ _)
  have hρ0 : 0 < ρ ^ C₀ := Real.rpow_pos_of_pos (by linarith) _
  have h2 : C ≤ |C| + 1 := by linarith [le_abs_self C]
  calc C * ρ ^ C₀ ≤ (|C| + 1) * ρ ^ C₀ := by gcongr
    _ ≤ (|C| + 1) * ρ ^ (max C₀ 0) := by gcongr

end HRS.MH.AdjointRd.Phase2SA12Near
