import HRS.MS.SA12X2J

/-!
# S.A.12 N8 (SA12X2), part K: the first-order kernel formula and the commutator `[ω, T_i]`

For `0 ≤ s < d`, `T_i = firstRiesz`: if `w ∈ C¹_c` with `|w(x)| ≤ M ‖y - x‖` then
`T_i w (y) = ∫ ∂_i g(y-x) w(x) dx` (`sa12x2_first_repr`), hence for a Lipschitz `C¹` coefficient `ω`:
`ω T_i v - T_i(ω v) = ∫ ∂_i g(y-x)(ω(y) - ω(x)) v(x) dx`, with kernel `≲ ‖y-x‖^{-s}` (locally integrable
for every `s < d`), and `‖1_B [ω, T_i] v‖₂ ≤ C L ρ^d ‖v‖₂` (`sa12x2_commT`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a HRS.MS.UniqN2b

variable {d : ℕ}

/-- The first-order kernel formula for a function vanishing at the evaluation point. -/
theorem sa12x2_first_repr (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d)
    {w : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w) (y : Euc d) {M : ℝ}
    (hM0 : 0 ≤ M) (hwb : ∀ x, |w x| ≤ M * ‖y - x‖ ^ (1 : ℝ)) :
    firstRiesz d s i w y = ∫ x, q09_H s i (y - x) * w x := by
  have hkg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  obtain ⟨a, A, ha0, had, hgb⟩ := sa12n_g_bound (d := d) hs0 2 (by push_cast; linarith)
  have hqb : ∀ z : Euc d, z ≠ 0 → |q09_H s i z| ≤ max 1 s * ‖z‖ ^ (-(s + 1)) := by
    intro z hz
    have := n0_qH_bound hs0 i hz
    rwa [show -(s + 1) = -s - 1 by ring]
  have hDc : Continuous (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) :=
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (fun x => fderiv ℝ w x (EuclideanSpace.single i 1)) :=
    (hwc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
      (by simp)
  have hI1 : Integrable (fun x => rieszKernel d s (y - x) *
      fderiv ℝ w x (EuclideanSpace.single i 1)) volume := n1a_conv_integrable hkg hDc hDcs y
  have hI2' : Integrable (fun x => q09_H s i (y - x) * w x) volume :=
    sa12n_integrable_of_pow hd y (n1a_H_meas s i).aestronglyMeasurable hw.continuous hwc
      (t := s + 1) (A := max 1 s) (M := M) (q := (1 : ℝ)) (by linarith) hqb hwb
  have hI2 : Integrable (fun x => fderiv ℝ (rieszKernel d s) (y - x) (EuclideanSpace.single i 1) *
      w x) volume := by
    refine hI2'.congr ((k3_ae_ne hd y).mono fun x hx => ?_)
    simp only
    rw [q09_H_eq_fderiv s i (sub_ne_zero.2 hx.symm)]
  have h1 := sa12n_weak_deriv hd i (fun z hz => n0_g_contDiffAt s hz) (a := a) (A := A) (M := M)
    (p := (1 : ℝ)) ha0 (by norm_num) hM0 (by have h := had; simp only [Nat.cast_ofNat] at h; linarith) hgb hw hwc y hwb hI1 hI2
  rw [sa12z3_firstRiesz_eq' hs0 hsd i hw hwc y]
  show ∫ x, rieszKernel d s (y - x) * fderiv ℝ w x (EuclideanSpace.single i 1) = _
  rw [h1]
  refine integral_congr_ae ((k3_ae_ne hd y).mono fun x hx => ?_)
  simp only
  rw [q09_H_eq_fderiv s i (sub_ne_zero.2 hx.symm)]

theorem sa12x2_first_lin {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {f1 f2 : Euc d → ℝ}
    (h1 : ContDiff ℝ 1 f1) (h1c : HasCompactSupport f1) (h2 : ContDiff ℝ 1 f2)
    (h2c : HasCompactSupport f2) (c : ℝ) (x : Euc d) :
    firstRiesz d s i (fun y => c * f1 y - f2 y) x =
      c * firstRiesz d s i f1 x - firstRiesz d s i f2 x := by
  have hkg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hD : ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      Integrable (fun t => rieszKernel d s (x - t) * D1 i f t) volume := fun f hf hfc =>
    n1a_conv_integrable hkg ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      ((hfc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single i 1))
        (by simp)) x
  have hdf : ∀ t, D1 i (fun y => c * f1 y - f2 y) t = c * D1 i f1 t - D1 i f2 t := by
    intro t
    have e1 : HasFDerivAt (fun y => c * f1 y) (c • fderiv ℝ f1 t) t :=
      ((h1.differentiable one_ne_zero) t).hasFDerivAt.const_mul c
    have e2 := e1.fun_sub ((h2.differentiable one_ne_zero) t).hasFDerivAt
    unfold D1
    rw [e2.fderiv]
    simp
  have hh : ContDiff ℝ 1 (fun y => c * f1 y - f2 y) := (contDiff_const.mul h1).sub h2
  rw [sa12z3_firstRiesz_eq' hs0 hsd i hh ((h1c.mul_left).sub h2c) x, sa12z3_firstRiesz_eq' hs0 hsd i h1 h1c x,
    sa12z3_firstRiesz_eq' hs0 hsd i h2 h2c x]
  simp_rw [hdf]
  have : (fun t => rieszKernel d s (x - t) * (c * D1 i f1 t - D1 i f2 t)) =
      fun t => c * (rieszKernel d s (x - t) * D1 i f1 t) - rieszKernel d s (x - t) * D1 i f2 t := by
    funext t; ring
  rw [this, integral_sub ((hD f1 h1 h1c).const_mul c) (hD f2 h2 h2c), integral_const_mul]

end HRS.MH.AdjointRd.Phase2SA12Near
