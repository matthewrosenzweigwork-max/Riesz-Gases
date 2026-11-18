import HRS.MS.R26T8AP09

/-!
# S8.2 T8A packet P15, part a: the pair Laplacian in centre and relative variables
For `Q` of class `C²` at `(x, y)`, with `X = (x+y)/2`, `z = x - y` and `midPair Q X z = Q (X + z/2) (X - z/2)`:
`Δ_x Q + Δ_y Q = ½ Δ_X midPair Q + 2 Δ_z midPair Q`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_p15_second_comp {E1 E2 : Type*} [NormedAddCommGroup E1] [NormedSpace ℝ E1]
    [NormedAddCommGroup E2] [NormedSpace ℝ E2] (U : E2 → ℝ) (c : E2) (L : E1 →L[ℝ] E2) (w : E1)
    (hU : ContDiffAt ℝ 2 U (c + L w)) (u v : E1) :
    fderiv ℝ (fderiv ℝ (fun w' => U (c + L w'))) w u v =
      fderiv ℝ (fderiv ℝ U) (c + L w) (L u) (L v) := by
  have hA : HasFDerivAt (fun w' : E1 => c + L w') L w := (L.hasFDerivAt).const_add c
  have hev : ∀ᶠ y in 𝓝 (c + L w), DifferentiableAt ℝ U y := by
    filter_upwards [hU.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hev' : ∀ᶠ w' in 𝓝 w, fderiv ℝ (fun w'' => U (c + L w'')) w' = (fderiv ℝ U (c + L w')).comp L := by
    filter_upwards [hA.continuousAt.eventually hev] with w' hw'
    exact (hw'.hasFDerivAt.comp w' (((L.hasFDerivAt).const_add c))).fderiv
  have h4 : fderiv ℝ (fderiv ℝ (fun w' => U (c + L w'))) w =
      fderiv ℝ (fun w' => (fderiv ℝ U (c + L w')).comp L) w := Filter.EventuallyEq.fderiv_eq hev'
  rw [h4]
  have hD : DifferentiableAt ℝ (fderiv ℝ U) (c + L w) :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h2 : HasFDerivAt (fun w' : E1 => fderiv ℝ U (c + L w')) ((fderiv ℝ (fderiv ℝ U) (c + L w)).comp L) w :=
    hD.hasFDerivAt.comp w hA
  have h3 := ((ContinuousLinearMap.precomp ℝ L).hasFDerivAt).comp w h2
  have h5 : HasFDerivAt (fun w' : E1 => (fderiv ℝ U (c + L w')).comp L)
      ((ContinuousLinearMap.precomp ℝ L).comp ((fderiv ℝ (fderiv ℝ U) (c + L w)).comp L)) w := h3
  rw [h5.fderiv]
  rfl

theorem r26t8a_p15_laplacian_split {d : ℕ} (Q : Euc d → Euc d → ℝ) (x y : Euc d)
    (hQ : ContDiffAt ℝ 2 (fun p : Euc d × Euc d => Q p.1 p.2) (x, y)) :
    Laplacian.laplacian (fun w => Q w y) x + Laplacian.laplacian (fun w => Q x w) y =
      (1 / 2) * Laplacian.laplacian (fun X => midPair Q X (x - y)) ((1 / 2 : ℝ) • (x + y)) +
        2 * Laplacian.laplacian (fun w => midPair Q ((1 / 2 : ℝ) • (x + y)) w) (x - y) := by
  set U : Euc d × Euc d → ℝ := fun p => Q p.1 p.2 with hU
  set B := fderiv ℝ (fderiv ℝ U) (x, y) with hB
  have hlap : ∀ f : Euc d → ℝ, Laplacian.laplacian f =
      fun w => ∑ i, fderiv ℝ (fderiv ℝ f) w ((stdOrthonormalBasis ℝ (Euc d)) i)
        ((stdOrthonormalBasis ℝ (Euc d)) i) := fun f => by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext w
    simp [iteratedFDeriv_two_apply]
  -- the four affine presentations
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
  have c1 := fun u v => r26t8a_p15_second_comp U ((0, y)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x
    (by rw [p1]; exact hQ) u v
  have c2 := fun u v => r26t8a_p15_second_comp U ((x, 0)) (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) y
    (by rw [p2]; exact hQ) u v
  have c3 := fun u v => r26t8a_p15_second_comp U (((1 / 2 : ℝ) • (x - y), -((1 / 2 : ℝ) • (x - y))))
    (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Euc d)) (ContinuousLinearMap.id ℝ (Euc d)))
    ((1 / 2 : ℝ) • (x + y)) (by rw [p3]; exact hQ) u v
  have c4 := fun u v => r26t8a_p15_second_comp U (((1 / 2 : ℝ) • (x + y), (1 / 2 : ℝ) • (x + y)))
    (ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d))
      (-((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)))) (x - y) (by rw [p4]; exact hQ) u v
  rw [p1] at c1; rw [p2] at c2; rw [p3] at c3; rw [p4] at c4
  rw [hlap, hlap, hlap, hlap]
  simp only [e1, e2, e3, e4, c1, c2, c3, c4, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  set v := (stdOrthonormalBasis ℝ (Euc d)) i
  have ha : ((ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ (Euc d)) (ContinuousLinearMap.id ℝ (Euc d))) v) =
      ((ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) v) + (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) v := by
    ext <;> simp
  have hb : ((ContinuousLinearMap.prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d))
        (-((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)))) v) =
      (1 / 2 : ℝ) • (((ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) v) - (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) v) := by
    ext <;> simp
  rw [ha, hb]
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

end HRS.MS.R26T8A
