import HRS.MS.R26T8AP15a

/-!
# S8.2 T8A packet P15, part b: the pair drift in centre and relative variables
With `X = (x+y)/2`, `z = x - y`: `<b_x, ∇_x Q> + <b_y, ∇_y Q> = <(b_x+b_y)/2, ∇_X midPair Q> + <b_x - b_y, ∇_z midPair Q>`.
The relative gradient is multiplied by `b_x - b_y`, which is the factor that carries the separation `|z|` when `b` is Lipschitz.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_p15_inner_gradient {d : ℕ} (f : Euc d → ℝ) (w v : Euc d) :
    inner ℝ v (gradient f w) = fderiv ℝ f w v := by
  rw [real_inner_comm]
  simp [gradient, InnerProductSpace.toDual_symm_apply]

theorem r26t8a_p15_first_comp {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] (U : E2 → ℝ) (c : E2) (L : E1 →L[ℝ] E2) (w : E1)
    (hU : DifferentiableAt ℝ U (c + L w)) (u : E1) :
    fderiv ℝ (fun w' => U (c + L w')) w u = fderiv ℝ U (c + L w) (L u) := by
  have hA : HasFDerivAt (fun w' : E1 => c + L w') L w := (L.hasFDerivAt).const_add c
  have h : HasFDerivAt (fun w' : E1 => U (c + L w')) ((fderiv ℝ U (c + L w)).comp L) w :=
    hU.hasFDerivAt.comp w hA
  rw [h.fderiv]
  rfl

theorem r26t8a_p15_drift_split {d : ℕ} (Q : Euc d → Euc d → ℝ) (x y bx bz : Euc d)
    (hQ : DifferentiableAt ℝ (fun p : Euc d × Euc d => Q p.1 p.2) (x, y)) :
    inner ℝ bx (gradient (fun w => Q w y) x) + inner ℝ bz (gradient (fun w => Q x w) y) =
      inner ℝ ((1 / 2 : ℝ) • (bx + bz)) (gradient (fun X => midPair Q X (x - y)) ((1 / 2 : ℝ) • (x + y))) +
        inner ℝ (bx - bz) (gradient (fun w => midPair Q ((1 / 2 : ℝ) • (x + y)) w) (x - y)) := by
  set U : Euc d × Euc d → ℝ := fun p => Q p.1 p.2 with hU
  simp only [r26t8a_p15_inner_gradient]
  have e1 : (fun w => Q w y) = fun w => U ((0, y) + (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) w) := by
    funext w; simp [hU]
  have e2 : (fun w => Q x w) = fun w => U ((x, 0) + (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) w) := by
    funext w; simp [hU]
  have e3 : (fun X => midPair Q X (x - y)) = fun X => U (((1 / 2 : ℝ) • (x - y), -((1 / 2 : ℝ) • (x - y))) +
      (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Euc d)) (ContinuousLinearMap.id ℝ (Euc d))) X) := by
    funext X; simp [hU, midPair, add_comm, sub_eq_add_neg]
  have e4 : (fun w => midPair Q ((1 / 2 : ℝ) • (x + y)) w) = fun w => U (((1 / 2 : ℝ) • (x + y), (1 / 2 : ℝ) • (x + y)) +
      (ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d))
        (-((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)))) w) := by
    funext w; simp [hU, midPair, sub_eq_add_neg]
  have p1 : ((0 : Euc d), y) + (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x = (x, y) := by simp
  have p2 : (x, (0 : Euc d)) + (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) y = (x, y) := by simp
  have p3 : ((1 / 2 : ℝ) • (x - y), -((1 / 2 : ℝ) • (x - y))) +
      (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Euc d)) (ContinuousLinearMap.id ℝ (Euc d)))
        ((1 / 2 : ℝ) • (x + y)) = (x, y) := by
    ext <;> simp <;> ring
  have p4 : ((1 / 2 : ℝ) • (x + y), (1 / 2 : ℝ) • (x + y)) +
      (ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d))
        (-((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)))) (x - y) = (x, y) := by
    ext <;> simp <;> ring
  have c1 := r26t8a_p15_first_comp U ((0, y)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x
    (by rw [p1]; exact hQ) bx
  have c2 := r26t8a_p15_first_comp U ((x, 0)) (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) y
    (by rw [p2]; exact hQ) bz
  have c3 := r26t8a_p15_first_comp U (((1 / 2 : ℝ) • (x - y), -((1 / 2 : ℝ) • (x - y))))
    (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Euc d)) (ContinuousLinearMap.id ℝ (Euc d)))
    ((1 / 2 : ℝ) • (x + y)) (by rw [p3]; exact hQ) ((1 / 2 : ℝ) • (bx + bz))
  have c4 := r26t8a_p15_first_comp U (((1 / 2 : ℝ) • (x + y), (1 / 2 : ℝ) • (x + y)))
    (ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d))
      (-((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)))) (x - y) (by rw [p4]; exact hQ) (bx - bz)
  rw [p1] at c1; rw [p2] at c2; rw [p3] at c3; rw [p4] at c4
  rw [e1, e2, e3, e4, c1, c2, c3, c4]
  have h3 : (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Euc d)) (ContinuousLinearMap.id ℝ (Euc d)))
      ((1 / 2 : ℝ) • (bx + bz)) = ((1 / 2 : ℝ) • (bx + bz), (1 / 2 : ℝ) • (bx + bz)) := rfl
  have h4 : (ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d))
      (-((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)))) (bx - bz) =
      ((1 / 2 : ℝ) • (bx - bz), -((1 / 2 : ℝ) • (bx - bz))) := rfl
  have h1 : ((ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) bx) = (bx, 0) := rfl
  have h2 : ((ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) bz) = (0, bz) := rfl
  rw [h1, h2, h3, h4, ← map_add, ← map_add]
  congr 1
  ext <;> simp <;> ring

end HRS.MS.R26T8A
