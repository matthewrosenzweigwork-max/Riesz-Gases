import HRS.MS.SA12NN2D

/-!
# S.A.12 N2 (SA12N), part E: the pointwise commutator formula and the case `s < d - 1`

For `a, v ∈ C²_b`, `v` compactly supported and `x` fixed, `w_x(y) = a(x) v(y) - a(y) v(y)` is in `C²_c` and
`a Hv(x) - H(a v)(x) = H(w_x)(x) = ∫ K(x-y) (a(x) - a(y)) v(y) dy` (`sa12n_hess_repr` with `p = 1`).
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

theorem sa12n_fderiv_apply_le {f : Euc d → ℝ} (hf : MemCb 2 f) (y : Euc d) (j : Fin d) :
    |fderiv ℝ f y (EuclideanSpace.single j 1)| ≤ cbNorm 2 f := by
  have h := (sa12z3_cb2_bounds hf y).2.1
  have := ContinuousLinearMap.le_opNorm (fderiv ℝ f y) (EuclideanSpace.single j (1 : ℝ))
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at this
  rw [← Real.norm_eq_abs]
  exact this.trans h

/-- The Hessian kernel formula for the Hessian entry itself (`hessRiesz i j = g * ∂_i ∂_j`). -/
theorem sa12n_hess_kernel (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hsp : s + 2 < d + p) {w : Euc d → ℝ} (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w)
    (i j : Fin d) (y : Euc d) {M M' : ℝ} (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M')
    (hwb : ∀ x, |w x| ≤ M * ‖y - x‖ ^ (p : ℝ))
    (hw'b : ∀ x, |D1 j w x| ≤ M' * ‖y - x‖ ^ ((p : ℝ) - 1)) :
    hessRiesz d s i j w y = ∫ x, q09_DH s i (y - x) (EuclideanSpace.single j 1) * w x := by
  have hsd : s < d := by
    have : (p : ℝ) ≤ 2 := by exact_mod_cast hp2
    linarith
  rw [sa12z3_hess_convFun hs0 hsd i j hw hwc y]
  exact sa12n_hess_repr hd hs0 p hp1 hp2 hsp hw hwc j i y hM0 hM'0 hwb hw'b

/-- The test function `w_x`. -/
def sa12n_wx (a v : Euc d → ℝ) (x : Euc d) : Euc d → ℝ := fun y => a x * v y - a y * v y

theorem sa12n_wx_contDiff {a v : Euc d → ℝ} (ha : ContDiff ℝ 2 a) (hv : ContDiff ℝ 2 v) (x : Euc d) :
    ContDiff ℝ 2 (sa12n_wx a v x) :=
  (contDiff_const.mul hv).sub (ha.mul hv)

theorem sa12n_wx_cs {a v : Euc d → ℝ} (hvc : HasCompactSupport v) (x : Euc d) :
    HasCompactSupport (sa12n_wx a v x) := by
  have h1 : HasCompactSupport (fun y => a x * v y) := hvc.mul_left
  have h2 : HasCompactSupport (fun y => a y * v y) := hvc.mul_left
  exact h1.sub h2

/-- The commutator as a value of `H` on `w_x`. -/
theorem sa12n_comm_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {a v : Euc d → ℝ}
    (ha : ContDiff ℝ 2 a) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (x : Euc d) :
    a x * hessRiesz d s i j v x - hessRiesz d s i j (fun y => a y * v y) x =
      hessRiesz d s i j (sa12n_wx a v x) x := by
  have h := sa12n_hess_lin hs0 hsd i j hv hvc (f2 := fun y => a y * v y) (ha.mul hv)
    (hvc.mul_left) (a x) x
  exact h.symm

/-- Bounds on `w_x` and its first derivative. -/
theorem sa12n_wx_bounds {a v : Euc d → ℝ} (ha : MemCb 2 a) (hv : MemCb 2 v) (x : Euc d) :
    (∀ y, |sa12n_wx a v x y| ≤ cbNorm 2 a * cbNorm 2 v * ‖x - y‖ ^ ((1 : ℕ) : ℝ)) ∧
    (∀ (j : Fin d) (y : Euc d), |D1 j (sa12n_wx a v x) y| ≤
      (3 * cbNorm 2 a * cbNorm 2 v) * ‖x - y‖ ^ (((1 : ℕ) : ℝ) - 1)) := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hv2 : ContDiff ℝ 2 v := by simpa using hv.1
  have hda : Differentiable ℝ a := ha2.differentiable (by norm_num)
  have hdv : Differentiable ℝ v := hv2.differentiable (by norm_num)
  have hA := sa12z3_cb_nonneg ha
  have hV := sa12z3_cb_nonneg hv
  refine ⟨fun y => ?_, fun j y => ?_⟩
  · have hl := sa12z3_a_lip ha x y
    have hvy := (sa12z3_cb2_bounds hv y).1
    simp only [sa12n_wx, Nat.cast_one, Real.rpow_one]
    rw [← sub_mul, abs_mul]
    calc |a x - a y| * |v y| ≤ (cbNorm 2 a * ‖x - y‖) * cbNorm 2 v :=
          mul_le_mul hl hvy (abs_nonneg _) (by positivity)
      _ = _ := by ring
  · simp only [Nat.cast_one, sub_self, Real.rpow_zero, mul_one]
    have hdw : fderiv ℝ (sa12n_wx a v x) y (EuclideanSpace.single j 1) =
        a x * fderiv ℝ v y (EuclideanSpace.single j 1) -
          (a y * fderiv ℝ v y (EuclideanSpace.single j 1) +
            v y * fderiv ℝ a y (EuclideanSpace.single j 1)) := by
      have h1 : HasFDerivAt (fun y => a x * v y) (a x • fderiv ℝ v y) y :=
        (hdv y).hasFDerivAt.const_mul (a x)
      have h2 : HasFDerivAt (fun y => a y * v y) (a y • fderiv ℝ v y + v y • fderiv ℝ a y) y :=
        (hda y).hasFDerivAt.mul (hdv y).hasFDerivAt
      have h3 := h1.fun_sub h2
      have : sa12n_wx a v x = fun y => a x * v y - a y * v y := rfl
      rw [this, h3.fderiv]
      simp
    show |fderiv ℝ (sa12n_wx a v x) y (EuclideanSpace.single j 1)| ≤ _
    rw [hdw]
    have b1 := sa12z3_cb2_bounds ha x
    have b2 := sa12z3_cb2_bounds ha y
    have b3 := sa12z3_cb2_bounds hv y
    have c1 := sa12n_fderiv_apply_le hv y j
    have c2 := sa12n_fderiv_apply_le ha y j
    calc |a x * fderiv ℝ v y (EuclideanSpace.single j 1) -
          (a y * fderiv ℝ v y (EuclideanSpace.single j 1) +
            v y * fderiv ℝ a y (EuclideanSpace.single j 1))|
        ≤ |a x * fderiv ℝ v y (EuclideanSpace.single j 1)| +
          (|a y * fderiv ℝ v y (EuclideanSpace.single j 1)| +
            |v y * fderiv ℝ a y (EuclideanSpace.single j 1)|) :=
          (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ cbNorm 2 a * cbNorm 2 v + (cbNorm 2 a * cbNorm 2 v + cbNorm 2 v * cbNorm 2 a) := by
          rw [abs_mul, abs_mul, abs_mul]
          gcongr
          · exact b1.1
          · exact b2.1
          · exact b3.1
      _ = _ := by ring

/-- Pointwise integral formula for the commutator when `s < d - 1`. -/
theorem sa12n_comm_pt_lt (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (i j : Fin d)
    {a v : Euc d → ℝ} (ha : MemCb 2 a) (hv : MemCb 2 v) (hvc : HasCompactSupport v) (x : Euc d) :
    a x * hessRiesz d s i j v x - hessRiesz d s i j (fun y => a y * v y) x =
      ∫ y, q09_DH s i (x - y) (EuclideanSpace.single j 1) * sa12n_wx a v x y := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hv2 : ContDiff ℝ 2 v := by simpa using hv.1
  have hsd : s < d := by linarith
  rw [sa12n_comm_eq hs0 hsd i j ha2 hv2 hvc x]
  obtain ⟨hb1, hb2⟩ := sa12n_wx_bounds ha hv x
  have hA := sa12z3_cb_nonneg ha
  have hV := sa12z3_cb_nonneg hv
  refine sa12n_hess_kernel hd hs0 1 le_rfl (by norm_num) (by push_cast; linarith)
    (sa12n_wx_contDiff ha2 hv2 x) (sa12n_wx_cs hvc x) i j x (by positivity) (by positivity)
    hb1 (fun y => hb2 j y)

end HRS.MH.AdjointRd.Phase2SA12Near
