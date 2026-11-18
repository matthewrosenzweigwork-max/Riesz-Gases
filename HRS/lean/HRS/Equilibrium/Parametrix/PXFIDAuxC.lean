import HRS.Equilibrium.Parametrix.PXFIDAuxB

/-!
# Packet PX-FID, file C: slices with a point singularity, pointwise bounds
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

/-- A function on the torus, smooth off the point `mk ã`, with the gradient and Hessian envelopes
of `PsiSize` (in the variable of the slice). -/
structure SingSlice (s K : ℝ) (ã : Euc d) (u : Torus d → ℝ) : Prop where
  smooth : ContDiffOn ℝ 2 (Torus.lift u) {p : Euc d | Torus.mk p ≠ Torus.mk ã}
  grad : ∀ p : Euc d, Torus.mk p ≠ Torus.mk ã →
    ‖fderiv ℝ (Torus.lift u) p‖ ≤ K * (1 + rTrunc (Torus.mk p) (Torus.mk ã) ^ (1 - s))
  hess : ∀ p : Euc d, Torus.mk p ≠ Torus.mk ã → ∀ j : Fin d,
    |fderiv ℝ (fderiv ℝ (Torus.lift u)) p (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| ≤
      K * (1 + rTrunc (Torus.mk p) (Torus.mk ã) ^ (-s))

theorem rTrunc_pos' {x y : Torus d} (h : x ≠ y) : 0 < rTrunc x y := PairCorrAux.rTrunc_pos h

theorem one_add_rpow_le_wEnv (hs : 1 ≤ s) (x y : Torus d) (h : x ≠ y) :
    1 + rTrunc x y ^ (1 - s) ≤ wEnv s x y := by
  have hr := rTrunc_pos' h
  have hr1 : rTrunc x y ≤ 1 := PairCorrAux.rTrunc_le_one x y
  unfold wEnv
  have : rTrunc x y ^ (1 - s) = rTrunc x y * rTrunc x y ^ (-s) := by
    rw [show (1 - s) = 1 + (-s) by ring, Real.rpow_add hr, Real.rpow_one]
  rw [this]
  have h2 : 0 ≤ rTrunc x y ^ (-s) := Real.rpow_nonneg hr.le _
  nlinarith

theorem SingSlice.norm_grad_le' {K : ℝ} {ã : Euc d} {u : Torus d → ℝ} (hu : SingSlice s K ã u)
    (x : Torus d) (hx : x ≠ Torus.mk ã) :
    ‖Torus.grad u x‖ ≤ K * (1 + rTrunc x (Torus.mk ã) ^ (1 - s)) := by
  have hmk : Torus.mk (Torus.rep x) = x := Torus.mk_rep x
  have hp : Torus.mk (Torus.rep x) ≠ Torus.mk ã := by rw [hmk]; exact hx
  have h1 := hu.grad _ hp
  rw [hmk] at h1
  have h2 : ‖Torus.grad u x‖ = ‖fderiv ℝ (Torus.lift u) (Torus.rep x)‖ := by
    unfold Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  rw [h2]
  exact h1

theorem SingSlice.norm_grad_le {K : ℝ} {ã : Euc d} {u : Torus d → ℝ} (hu : SingSlice s K ã u)
    (hK : 0 ≤ K) (hs : 1 ≤ s) (x : Torus d) (hx : x ≠ Torus.mk ã) :
    ‖Torus.grad u x‖ ≤ K * wEnv s x (Torus.mk ã) := by
  have hmk : Torus.mk (Torus.rep x) = x := Torus.mk_rep x
  have hp : Torus.mk (Torus.rep x) ≠ Torus.mk ã := by rw [hmk]; exact hx
  have h1 := hu.grad _ hp
  rw [hmk] at h1
  have h2 : ‖Torus.grad u x‖ = ‖fderiv ℝ (Torus.lift u) (Torus.rep x)‖ := by
    unfold Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  rw [h2]
  exact h1.trans (mul_le_mul_of_nonneg_left (one_add_rpow_le_wEnv hs x _ hx) hK)

theorem SingSlice.abs_laplacian_le {K : ℝ} {ã : Euc d} {u : Torus d → ℝ} (hu : SingSlice s K ã u)
    (x : Torus d) (hx : x ≠ Torus.mk ã) :
    |Torus.laplacian u x| ≤ d * K * wEnv s x (Torus.mk ã) := by
  have hmk : Torus.mk (Torus.rep x) = x := Torus.mk_rep x
  have hp : Torus.mk (Torus.rep x) ≠ Torus.mk ã := by rw [hmk]; exact hx
  have h1 := hu.hess _ hp
  rw [hmk] at h1
  rw [laplacian_eq_sum_fderiv]
  have h3 : ∀ j : Fin d, |fderiv ℝ (fderiv ℝ (Torus.lift u)) (Torus.rep x)
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)| ≤ K * wEnv s x (Torus.mk ã) := by
    intro j
    exact (h1 j).trans (le_of_eq (by unfold wEnv; ring))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j : Fin d, |fderiv ℝ (fderiv ℝ (Torus.lift u)) (Torus.rep x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)|
      ≤ ∑ _j : Fin d, K * wEnv s x (Torus.mk ã) := Finset.sum_le_sum fun j _ => h3 j
    _ = d * K * wEnv s x (Torus.mk ã) := by simp; ring

end HRS.Parx.PXFID

end
