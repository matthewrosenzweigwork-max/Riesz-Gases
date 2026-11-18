import HRS.MS.SA12X2B

/-!
# S.A.12 N2 endpoint (SA12X2), part C: Taylor decomposition of the commutator and the remainder bound

`a Hv(x) - H(a v)(x) = Σ_l ∂_l a(x) Q_l(x) - H(r_x v)(x)`, `Q_l = x_l H v - H(y_l v)`, and
`|H(r_x v)(x)| ≤ ∫ m cb ‖x-y‖^{-s} |v(y)| dy` for `0 ≤ s < d`.
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

theorem sa12x2_fderiv_sum (L : Euc d →L[ℝ] ℝ) (z : Euc d) :
    L z = ∑ l, z l * L (EuclideanSpace.single l 1) := by
  conv_lhs => rw [show z = ∑ l, z l • (EuclideanSpace.single l (1 : ℝ) : Euc d) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  simp [map_sum, smul_eq_mul]

/-- The Taylor decomposition of the commutator. -/
theorem sa12x2_comm_decomp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {a v : Euc d → ℝ}
    (ha : MemCb 2 a) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (x : Euc d) :
    a x * hessRiesz d s i j v x - hessRiesz d s i j (fun y => a y * v y) x =
      ∑ l, fderiv ℝ a x (EuclideanSpace.single l 1) *
          (x l * hessRiesz d s i j v x - hessRiesz d s i j (fun y => y l * v y) x) -
        hessRiesz d s i j (fun y => sa12x2_r a x y * v y) x := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  rw [sa12n_comm_eq hs0 hsd i j ha2 hv hvc x]
  set g : Fin d → ℝ := fun l => fderiv ℝ a x (EuclideanSpace.single l 1) with hg
  set f : Fin d → Euc d → ℝ := fun l y => x l * v y - y l * v y with hf
  have hfd : ∀ l, ContDiff ℝ 2 (f l) := fun l =>
    (contDiff_const.mul hv).sub ((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).contDiff.mul hv)
  have hfc : ∀ l, HasCompactSupport (f l) := fun l => (hvc.mul_left).sub (hvc.mul_left)
  obtain ⟨⟨hAd, hAc⟩, hAe⟩ := sa12x2_hess_sum hs0 hsd i j hfd hfc g Finset.univ x
  have hBd : ContDiff ℝ 2 (fun y => sa12x2_r a x y * v y) := (sa12x2_r_contDiff ha2 x).mul hv
  have hBc : HasCompactSupport (fun y => sa12x2_r a x y * v y) := hvc.mul_left
  have hw : sa12n_wx a v x = fun y => 1 * (∑ l ∈ Finset.univ, g l * f l y) -
      sa12x2_r a x y * v y := by
    funext y
    have h1 : ∑ l, g l * f l y = v y * fderiv ℝ a x (x - y) := by
      rw [sa12x2_fderiv_sum (fderiv ℝ a x) (x - y), Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hg, hf, PiLp.sub_apply]; ring
    have h2 : fderiv ℝ a x (y - x) = - fderiv ℝ a x (x - y) := by
      rw [← map_neg]; congr 1; abel
    simp only [sa12n_wx, sa12x2_r]
    rw [h1, h2]; ring
  rw [hw, sa12n_hess_lin hs0 hsd i j hAd hAc hBd hBc 1 x, hAe, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  have hl := sa12n_hess_lin hs0 hsd i j hv hvc (f2 := fun y => y l * v y)
    ((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).contDiff.mul hv) (hvc.mul_left) (x l) x
  rw [show hessRiesz d s i j (f l) x = _ from hl]

/-- The pointwise bound of the Taylor remainder term. -/
theorem sa12x2_E_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d)
    {a v : Euc d → ℝ} (ha : MemCb 2 a) (hv : MemCb 2 v) (hvc : HasCompactSupport v) (x : Euc d) :
    ‖hessRiesz d s i j (fun y => sa12x2_r a x y * v y) x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal ((max 1 s * (s + 3) * cbNorm 2 a) * ‖x - y‖ ^ (-s)) * ‖v y‖ₑ := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hv2 : ContDiff ℝ 2 v := by simpa using hv.1
  have hda : Differentiable ℝ a := ha2.differentiable (by norm_num)
  have hdv : Differentiable ℝ v := hv2.differentiable (by norm_num)
  have hA := sa12z3_cb_nonneg ha
  have hV := sa12z3_cb_nonneg hv
  set m : ℝ := max 1 s * (s + 3) with hm
  have hm0 : 0 ≤ m := by
    have : (0 : ℝ) ≤ max 1 s := le_trans zero_le_one (le_max_left _ _)
    positivity
  have hwd : ContDiff ℝ 2 (fun y => sa12x2_r a x y * v y) := (sa12x2_r_contDiff ha2 x).mul hv2
  have hwc : HasCompactSupport (fun y => sa12x2_r a x y * v y) := hvc.mul_left
  have hker := sa12n_hess_kernel hd hs0 2 (by norm_num) le_rfl (by push_cast; linarith) hwd hwc i j x
    (M := cbNorm 2 a * cbNorm 2 v) (M' := 3 * cbNorm 2 a * cbNorm 2 v) (by positivity)
    (by positivity)
    (fun y => by
      have h1 := sa12x2_r_bound1 ha x y
      have h2 := (sa12z3_cb2_bounds hv y).1
      rw [Real.rpow_natCast, abs_mul]
      calc |sa12x2_r a x y| * |v y| ≤ (cbNorm 2 a * ‖x - y‖ ^ 2) * cbNorm 2 v :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = _ := by push_cast; ring)
    (fun y => by
      have hr := sa12x2_r_hasFDeriv ha2 x y
      have h3 : HasFDerivAt (fun y => sa12x2_r a x y * v y)
          (sa12x2_r a x y • fderiv ℝ v y + v y • (fderiv ℝ a y - fderiv ℝ a x)) y :=
        hr.mul (hdv y).hasFDerivAt
      have e : D1 j (fun y => sa12x2_r a x y * v y) y =
          sa12x2_r a x y * D1 j v y + v y * D1 j (sa12x2_r a x) y := by
        simp only [D1, h3.fderiv, hr.fderiv]
        simp
      have b1 := sa12x2_r_bound2 ha x y
      have b2 := sa12x2_r_deriv ha x j y
      have b3 : |D1 j v y| ≤ cbNorm 2 v := sa12n_fderiv_apply_le hv y j
      have b4 := (sa12z3_cb2_bounds hv y).1
      have hn : (((2 : ℕ) : ℝ) - 1) = 1 := by norm_num
      rw [hn, Real.rpow_one, e]
      calc |sa12x2_r a x y * D1 j v y + v y * D1 j (sa12x2_r a x) y|
          ≤ |sa12x2_r a x y| * |D1 j v y| + |v y| * |D1 j (sa12x2_r a x) y| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul]
      _ ≤ (2 * cbNorm 2 a * ‖x - y‖) * cbNorm 2 v + cbNorm 2 v * (cbNorm 2 a * ‖x - y‖) := by
            gcongr
      _ = _ := by ring)
  rw [hker]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [k3_ae_ne hd x] with y hy
  have hz : x - y ≠ 0 := sub_ne_zero.2 hy.symm
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hz
  rw [← ofReal_norm, ← ofReal_norm (v y), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hK := n0_qDH_bound hs0 i j hz
  have hr := sa12x2_r_bound1 ha x y
  have e : ‖x - y‖ ^ (-s - 2) * ‖x - y‖ ^ 2 = ‖x - y‖ ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]; congr 1; push_cast; ring
  have hpow : 0 ≤ ‖x - y‖ ^ (-s - 2) := by positivity
  calc ‖q09_DH s i (x - y) (EuclideanSpace.single j 1) * (sa12x2_r a x y * v y)‖
      = |q09_DH s i (x - y) (EuclideanSpace.single j 1)| * (|sa12x2_r a x y| * |v y|) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
    _ ≤ (m * ‖x - y‖ ^ (-s - 2)) * ((cbNorm 2 a * ‖x - y‖ ^ 2) * |v y|) :=
        mul_le_mul hK (mul_le_mul_of_nonneg_right hr (abs_nonneg _)) (by positivity) (by positivity)
    _ = (m * cbNorm 2 a * ‖x - y‖ ^ (-s)) * ‖v y‖ := by
        rw [← e, Real.norm_eq_abs]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
