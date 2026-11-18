import HRS.MS.R26T8AP15h
import HRS.MS.R26T8AP15b

/-!
# S8.2 T8A P15i: centre/relative splits of the pair Laplacian and drift in terms of `pdir`
With `e i = EuclideanSpace.single i 1`, `PP G = Σ_i pdir (e_i,0) (pdir (e_i,0) G)` (= `Δ_X midPair G`) and
`ZZ G = Σ_i pdir (0,e_i) (pdir (0,e_i) G)` (= `Δ_z midPair G`):
* `Δ_x G + Δ_y G = ½ PP G + 2 ZZ G` at `x ≠ y` (`G` is `C²` there);
* `<b_x,∇_x G> + <b_y,∇_y G> = Σ_i ½(b_x+b_y)_i pdir (e_i,0) G + Σ_i (b_x-b_y)_i pdir (0,e_i) G`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The `i`-th coordinate vector. -/
def r26t8a_e (d : ℕ) (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

theorem r26t8a_e_norm (i : Fin d) : ‖r26t8a_e d i‖ = 1 := by simp [r26t8a_e]

def r26t8a_PP (G : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  ∑ i : Fin d, r26t8a_pdir (r26t8a_e d i, 0) (r26t8a_pdir (r26t8a_e d i, 0) G) x y

def r26t8a_ZZ (G : Euc d → Euc d → ℝ) (x y : Euc d) : ℝ :=
  ∑ i : Fin d, r26t8a_pdir (0, r26t8a_e d i) (r26t8a_pdir (0, r26t8a_e d i) G) x y

theorem r26t8a_laplacian_basis (f : Euc d → ℝ) :
    Laplacian.laplacian f = fun w => ∑ i : Fin d, fderiv ℝ (fderiv ℝ f) w (r26t8a_e d i) (r26t8a_e d i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin d) ℝ)]
  funext w
  simp [iteratedFDeriv_two_apply, r26t8a_e]

theorem r26t8a_pdir_second {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hΦ : ContDiffAt ℝ 2 (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((1 / 2 : ℝ) • (x + y), x - y))
    (u v : Euc d × Euc d) :
    r26t8a_pdir u (r26t8a_pdir v G) x y =
      fderiv ℝ (fderiv ℝ (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2)) ((1 / 2 : ℝ) • (x + y), x - y) u v := by
  set Φ : Euc d × Euc d → ℝ := fun Yw => midPair G Yw.1 Yw.2 with hΦdef
  set p : Euc d × Euc d := ((1 / 2 : ℝ) • (x + y), x - y) with hp
  have hfun : (fun Yw : Euc d × Euc d => midPair (r26t8a_pdir v G) Yw.1 Yw.2) =
      fun Yw => (ContinuousLinearMap.apply ℝ ℝ v) (fderiv ℝ Φ Yw) := by
    funext Yw
    rw [r26t8a_midPair_pdir]
    rfl
  have hD : DifferentiableAt ℝ (fderiv ℝ Φ) p :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  show fderiv ℝ (fun Yw : Euc d × Euc d => midPair (r26t8a_pdir v G) Yw.1 Yw.2) p u = _
  rw [hfun]
  have h2 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp p hD.hasFDerivAt
  have h3 : fderiv ℝ (fun Yw => (ContinuousLinearMap.apply ℝ ℝ v) (fderiv ℝ Φ Yw)) p =
      (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ Φ) p) := h2.fderiv
  rw [h3]
  rfl

theorem r26t8a_midPair_contDiffAt {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hG : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => G q.1 q.2) (x, y)) :
    ContDiffAt ℝ 2 (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((1 / 2 : ℝ) • (x + y), x - y) := by
  have hL : ContDiff ℝ 2 (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) :=
    (contDiff_fst.add (contDiff_snd.const_smul _)).prodMk (contDiff_fst.sub (contDiff_snd.const_smul _))
  have hpt : (((1 / 2 : ℝ) • (x + y)) + (1 / 2 : ℝ) • (x - y), ((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (x - y)) =
      (x, y) := Prod.ext (by module) (by module)
  have hg : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => G q.1 q.2)
      ((fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2))
        ((1 / 2 : ℝ) • (x + y), x - y)) := by
    show ContDiffAt ℝ 2 (fun q : Euc d × Euc d => G q.1 q.2) (((1 / 2 : ℝ) • (x + y)) + (1 / 2 : ℝ) • (x - y),
      ((1 / 2 : ℝ) • (x + y)) - (1 / 2 : ℝ) • (x - y))
    rw [hpt]; exact hG
  exact ContDiffAt.comp ((1 / 2 : ℝ) • (x + y), x - y) hg hL.contDiffAt

theorem r26t8a_p15_PP {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hG : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => G q.1 q.2) (x, y)) :
    Laplacian.laplacian (fun X => midPair G X (x - y)) ((1 / 2 : ℝ) • (x + y)) = r26t8a_PP G x y := by
  have hΦ := r26t8a_midPair_contDiffAt hG
  unfold r26t8a_PP
  rw [r26t8a_laplacian_basis]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [r26t8a_pdir_second hΦ]
  have e : (fun X => midPair G X (x - y)) = fun w' =>
      (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((0, x - y) + (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) w') := by
    funext w'; simp
  rw [e]
  have hpt : ((0, x - y) : Euc d × Euc d) + (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) ((1 / 2 : ℝ) • (x + y)) =
      ((1 / 2 : ℝ) • (x + y), x - y) := by simp
  have := r26t8a_p15_second_comp (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) (0, x - y)
    (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) ((1 / 2 : ℝ) • (x + y)) (by rw [hpt]; exact hΦ)
    (r26t8a_e d i) (r26t8a_e d i)
  rw [hpt] at this
  rw [this]
  rfl

theorem r26t8a_p15_ZZ {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hG : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => G q.1 q.2) (x, y)) :
    Laplacian.laplacian (fun w => midPair G ((1 / 2 : ℝ) • (x + y)) w) (x - y) = r26t8a_ZZ G x y := by
  have hΦ := r26t8a_midPair_contDiffAt hG
  unfold r26t8a_ZZ
  rw [r26t8a_laplacian_basis]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [r26t8a_pdir_second hΦ]
  have e : (fun w => midPair G ((1 / 2 : ℝ) • (x + y)) w) = fun w' =>
      (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) (((1 / 2 : ℝ) • (x + y), 0) +
        (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) w') := by
    funext w'; simp
  rw [e]
  have hpt : (((1 / 2 : ℝ) • (x + y), (0 : Euc d)) : Euc d × Euc d) +
      (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (x - y) = ((1 / 2 : ℝ) • (x + y), x - y) := by simp
  have := r26t8a_p15_second_comp (fun Yw : Euc d × Euc d => midPair G Yw.1 Yw.2) ((1 / 2 : ℝ) • (x + y), 0)
    (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (x - y) (by rw [hpt]; exact hΦ)
    (r26t8a_e d i) (r26t8a_e d i)
  rw [hpt] at this
  rw [this]
  rfl

theorem r26t8a_p15_lap_pdir {G : Euc d → Euc d → ℝ} {x y : Euc d}
    (hG : ContDiffAt ℝ 2 (fun q : Euc d × Euc d => G q.1 q.2) (x, y)) :
    Laplacian.laplacian (fun w => G w y) x + Laplacian.laplacian (fun w => G x w) y =
      (1 / 2) * r26t8a_PP G x y + 2 * r26t8a_ZZ G x y := by
  rw [r26t8a_p15_laplacian_split G x y hG, r26t8a_p15_PP hG, r26t8a_p15_ZZ hG]

end HRS.MS.R26T8A
