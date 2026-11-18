import HRS.MS.SA12X2A

/-!
# S.A.12 N2 endpoint (SA12X2), part B: linearity of `hessRiesz` over finite sums and the Taylor remainder

`r_x(y) = a(y) - a(x) - Da(x)(y-x)`: `|r_x(y)| ≤ min(cb ‖x-y‖², 2 cb ‖x-y‖)`, `|∂_j r_x(y)| ≤ cb ‖x-y‖`
for `a ∈ C²_b` with `cb = cbNorm 2 a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MS.UniqN3a HRS.MS.UniqN2b

variable {d : ℕ}

theorem sa12x2_hess_zero (s : ℝ) (i j : Fin d) (x : Euc d) :
    hessRiesz d s i j (fun _ => (0 : ℝ)) x = 0 := by
  simp [hessRiesz]

theorem sa12x2_hess_add {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {f1 f2 : Euc d → ℝ}
    (h1 : ContDiff ℝ 2 f1) (h1c : HasCompactSupport f1) (h2 : ContDiff ℝ 2 f2)
    (h2c : HasCompactSupport f2) (c : ℝ) (x : Euc d) :
    hessRiesz d s i j (fun y => c * f1 y + f2 y) x =
      c * hessRiesz d s i j f1 x + hessRiesz d s i j f2 x := by
  have hneg : hessRiesz d s i j (fun y => -f2 y) x = - hessRiesz d s i j f2 x := by
    have h0c : HasCompactSupport (fun _ : Euc d => (0 : ℝ)) :=
      (HasCompactSupport.zero : HasCompactSupport (0 : Euc d → ℝ))
    have := sa12n_hess_lin hs0 hsd i j h2 h2c (f2 := fun _ => (0 : ℝ)) contDiff_const h0c (-1) x
    rw [sa12x2_hess_zero] at this
    simp only [neg_mul, one_mul, sub_zero] at this
    linarith
  have := sa12n_hess_lin hs0 hsd i j h1 h1c (f2 := fun y => -f2 y) h2.neg h2c.neg c x
  simp only [sub_neg_eq_add] at this
  rw [this, hneg]; ring

theorem sa12x2_hess_sum {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d)
    {f : Fin d → Euc d → ℝ} (hf : ∀ l, ContDiff ℝ 2 (f l)) (hfc : ∀ l, HasCompactSupport (f l))
    (c : Fin d → ℝ) (S : Finset (Fin d)) (x : Euc d) :
    (ContDiff ℝ 2 (fun y => ∑ l ∈ S, c l * f l y) ∧
      HasCompactSupport (fun y => ∑ l ∈ S, c l * f l y)) ∧
    hessRiesz d s i j (fun y => ∑ l ∈ S, c l * f l y) x =
      ∑ l ∈ S, c l * hessRiesz d s i j (f l) x := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨contDiff_const, (HasCompactSupport.zero : HasCompactSupport (0 : Euc d → ℝ))⟩,
      sa12x2_hess_zero s i j x⟩
  | insert a S ha ih =>
    obtain ⟨⟨ihd, ihc⟩, ihe⟩ := ih
    have e : (fun y => ∑ l ∈ insert a S, c l * f l y) = fun y => c a * f a y + ∑ l ∈ S, c l * f l y := by
      funext y; rw [Finset.sum_insert ha]
    rw [e]
    refine ⟨⟨(contDiff_const.mul (hf a)).add ihd, ((hfc a).mul_left).add ihc⟩, ?_⟩
    rw [sa12x2_hess_add hs0 hsd i j (hf a) (hfc a) ihd ihc (c a) x, ihe, Finset.sum_insert ha]

/-- The Taylor remainder of `a` at `x`. -/
def sa12x2_r (a : Euc d → ℝ) (x y : Euc d) : ℝ := a y - a x - fderiv ℝ a x (y - x)

theorem sa12x2_r_contDiff {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) (x : Euc d) :
    ContDiff ℝ 2 (sa12x2_r a x) := by
  unfold sa12x2_r
  exact (ha.sub contDiff_const).sub ((fderiv ℝ a x).contDiff.comp (contDiff_id.sub contDiff_const))

theorem sa12x2_fderiv_lip {a : Euc d → ℝ} (ha : MemCb 2 a) (x y : Euc d) :
    ‖fderiv ℝ a y - fderiv ℝ a x‖ ≤ cbNorm 2 a * ‖y - x‖ := by
  have hl := (sa12z3_a_c11 ha).2.2.2
  have := hl.dist_le_mul y x
  rwa [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (sa12z3_cb_nonneg ha)] at this

theorem sa12x2_r_hasFDeriv {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) (x y : Euc d) :
    HasFDerivAt (sa12x2_r a x) (fderiv ℝ a y - fderiv ℝ a x) y := by
  have hda : DifferentiableAt ℝ a y := (ha.differentiable (by norm_num)) y
  have h1 : HasFDerivAt (fun z => a z - a x) (fderiv ℝ a y) y := hda.hasFDerivAt.sub_const _
  have h2 : HasFDerivAt (fun z : Euc d => fderiv ℝ a x (z - x)) (fderiv ℝ a x) y := by
    have := (fderiv ℝ a x).hasFDerivAt (x := y - x)
    have h3 : HasFDerivAt (fun z : Euc d => z - x) (ContinuousLinearMap.id ℝ (Euc d)) y :=
      (hasFDerivAt_id y).sub_const x
    exact (this.comp y h3).congr_fderiv (by ext; simp)
  exact h1.sub h2

theorem sa12x2_r_bound2 {a : Euc d → ℝ} (ha : MemCb 2 a) (x y : Euc d) :
    |sa12x2_r a x y| ≤ 2 * cbNorm 2 a * ‖x - y‖ := by
  have hl := sa12z3_a_lip ha y x
  have hb := (sa12z3_cb2_bounds ha x).2.1
  have hop := (fderiv ℝ a x).le_opNorm (y - x)
  have hn : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
  have hA := sa12z3_cb_nonneg ha
  unfold sa12x2_r
  rw [← Real.norm_eq_abs]
  calc ‖a y - a x - fderiv ℝ a x (y - x)‖ ≤ ‖a y - a x‖ + ‖fderiv ℝ a x (y - x)‖ := norm_sub_le _ _
    _ ≤ cbNorm 2 a * ‖y - x‖ + cbNorm 2 a * ‖y - x‖ := by
        rw [Real.norm_eq_abs]
        exact add_le_add hl (hop.trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))
    _ = 2 * cbNorm 2 a * ‖x - y‖ := by rw [hn]; ring

theorem sa12x2_r_deriv {a : Euc d → ℝ} (ha : MemCb 2 a) (x : Euc d) (j : Fin d) (y : Euc d) :
    |D1 j (sa12x2_r a x) y| ≤ cbNorm 2 a * ‖x - y‖ := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have h := sa12x2_r_hasFDeriv ha2 x y
  have e : D1 j (sa12x2_r a x) y = (fderiv ℝ a y - fderiv ℝ a x) (EuclideanSpace.single j 1) := by
    unfold D1; rw [h.fderiv]
  rw [e, ← Real.norm_eq_abs]
  have hop := (fderiv ℝ a y - fderiv ℝ a x).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  simp only [PiLp.norm_single, norm_one, mul_one] at hop
  refine hop.trans ?_
  rw [norm_sub_rev x y]
  exact sa12x2_fderiv_lip ha x y

theorem sa12x2_r_bound1 {a : Euc d → ℝ} (ha : MemCb 2 a) (x y : Euc d) :
    |sa12x2_r a x y| ≤ cbNorm 2 a * ‖x - y‖ ^ 2 := by
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have hA := sa12z3_cb_nonneg ha
  set R : ℝ := ‖y - x‖ with hR
  have hxy : ‖x - y‖ = R := norm_sub_rev _ _
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ) (f := sa12x2_r a x)
    (f' := fun z => fderiv ℝ a z - fderiv ℝ a x) (s := closedBall x R) (C := cbNorm 2 a * R)
    (fun z _ => (sa12x2_r_hasFDeriv ha2 x z).hasFDerivWithinAt)
    (fun z hz => by
      refine (sa12x2_fderiv_lip ha x z).trans ?_
      have : ‖z - x‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hz
      exact mul_le_mul_of_nonneg_left this hA)
    (convex_closedBall x R) (mem_closedBall_self (norm_nonneg _))
    (y := y) (by rw [mem_closedBall, dist_eq_norm])
  have h0 : sa12x2_r a x x = 0 := by simp [sa12x2_r]
  rw [h0, sub_zero, Real.norm_eq_abs] at hmv
  rw [hxy]
  calc |sa12x2_r a x y| ≤ cbNorm 2 a * R * ‖y - x‖ := hmv
    _ = cbNorm 2 a * R ^ 2 := by rw [← hR]; ring

end HRS.MH.AdjointRd.Phase2SA12Near
