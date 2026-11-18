import HRS.MS.R26T8AP15i

/-!
# S8.2 T8A P15j: the drift split in terms of `pdir`
`<b_x,∇_x G> + <b_y,∇_y G> = Σ_i ½(b_x+b_y)_i pdir (e_i,0) G + Σ_i (b_x-b_y)_i pdir (0,e_i) G` (`G` differentiable at `(x,y)`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_clm_expand (L : Euc d →L[ℝ] ℝ) (v : Euc d) : L v = ∑ i : Fin d, v i * L (r26t8a_e d i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  simp [r26t8a_e]

theorem r26t8a_midPair_differentiableAt {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hG : DifferentiableAt ℝ (fun q : Euc d × Euc d => G q.1 q.2) (x, y)) :
    DifferentiableAt ℝ (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((1 / 2 : ℝ) • (x + y), x - y) := by
  have hL : Differentiable ℝ (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) :=
    (differentiable_fst.add (differentiable_snd.const_smul (1 / 2 : ℝ))).prodMk
      (differentiable_fst.sub (differentiable_snd.const_smul (1 / 2 : ℝ)))
  have hpt : (((1 / 2 : ℝ) • (x + y)) + (1 / 2 : ℝ) • (x - y), ((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (x - y)) =
      (x, y) := Prod.ext (by module) (by module)
  have hg : DifferentiableAt ℝ (fun q : Euc d × Euc d => G q.1 q.2)
      ((fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2))
        ((1 / 2 : ℝ) • (x + y), x - y)) := by
    show DifferentiableAt ℝ (fun q : Euc d × Euc d => G q.1 q.2) (((1 / 2 : ℝ) • (x + y)) + (1 / 2 : ℝ) • (x - y),
      ((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (x - y))
    rw [hpt]; exact hG
  exact DifferentiableAt.comp ((1 / 2 : ℝ) • (x + y), x - y) hg (hL _)

theorem r26t8a_p15_drift_pdir {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hG : DifferentiableAt ℝ (fun q : Euc d × Euc d => G q.1 q.2) (x, y)) (bx bz : Euc d) :
    inner ℝ bx (gradient (fun w => G w y) x) + inner ℝ bz (gradient (fun w => G x w) y) =
      ∑ i : Fin d, (1 / 2 : ℝ) * (bx i + bz i) * r26t8a_pdir (r26t8a_e d i, 0) G x y +
      ∑ i : Fin d, (bx i - bz i) * r26t8a_pdir (0, r26t8a_e d i) G x y := by
  have hΦ := r26t8a_midPair_differentiableAt hG
  rw [r26t8a_p15_drift_split G x y bx bz hG]
  simp only [r26t8a_p15_inner_gradient]
  have e1 : (fun X => midPair G X (x - y)) = fun w' =>
      (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((0, x - y) + (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) w') := by
    funext w'; simp
  have e2 : (fun w => midPair G ((1 / 2 : ℝ) • (x + y)) w) = fun w' =>
      (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) (((1 / 2 : ℝ) • (x + y), 0) +
        (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) w') := by
    funext w'; simp
  have hpt1 : ((0, x - y) : Euc d × Euc d) + (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) ((1 / 2 : ℝ) • (x + y)) =
      ((1 / 2 : ℝ) • (x + y), x - y) := by simp
  have hpt2 : (((1 / 2 : ℝ) • (x + y), (0 : Euc d)) : Euc d × Euc d) +
      (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (x - y) = ((1 / 2 : ℝ) • (x + y), x - y) := by simp
  have c1 := fun u => r26t8a_p15_first_comp (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) (0, x - y)
    (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) ((1 / 2 : ℝ) • (x + y)) (by rw [hpt1]; exact hΦ) u
  have c2 := fun u => r26t8a_p15_first_comp (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((1 / 2 : ℝ) • (x + y), 0)
    (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (x - y) (by rw [hpt2]; exact hΦ) u
  rw [hpt1] at c1; rw [hpt2] at c2
  rw [r26t8a_clm_expand (fderiv ℝ (fun X => midPair G X (x - y)) ((1 / 2 : ℝ) • (x + y)))]
  rw [r26t8a_clm_expand (fderiv ℝ (fun w => midPair G ((1 / 2 : ℝ) • (x + y)) w) (x - y))]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [e1, c1 (r26t8a_e d i)]
    simp only [r26t8a_pdir, ContinuousLinearMap.inl_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2, c2 (r26t8a_e d i)]
    simp only [r26t8a_pdir, ContinuousLinearMap.inr_apply, PiLp.sub_apply]

end HRS.MS.R26T8A
