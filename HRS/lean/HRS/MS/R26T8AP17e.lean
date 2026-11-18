import HRS.MS.R26T8AP17d

/-!
# S8.2 local Newton layer, packet T8A.P17 (part e): the commutator kernel `hSource f` is conormal of order `criticalS d`
`r26t8a_p17_h_conormal`: `TestBound (k+2) A f` implies `Conormal k 0 0 (criticalS d) (C*A) (hSource f)`, `C` depending on `d, k` only
(the gain of one relative power comes from the gradient difference before differentiating).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p17_h_eq (hd : 2 ≤ d) (f : Euc d → ℝ) (x y : Euc d) :
    hSource f x y = fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d)) (x - y) (gradient f x - gradient f y) := by
  unfold hSource commutatorKernel rieszKernelGrad
  rw [r26t8a_p17_rk_eq hd, real_inner_comm]
  simp [gradient]

theorem r26t8a_p17_mid_eq (hd : 2 ≤ d) (f : Euc d → ℝ) (Y w : Euc d) :
    midPair (hSource f) Y w =
      (ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)) (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d)) w)
        (r26t8a_p17_G f (Y, w)) := by
  unfold midPair
  rw [r26t8a_p17_h_eq hd]
  have e : Y + (1 / 2 : ℝ) • w - (Y - (1 / 2 : ℝ) • w) = w := by module
  have e2 : Y - (1 / 2 : ℝ) • w = Y + (-(1 / 2 : ℝ)) • w := by module
  rw [e, e2]
  rfl

theorem r26t8a_p17_g_contDiffAt (hd : 2 ≤ d) {w : Euc d} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ (fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d))) w := by
  have h1 : ContDiffAt ℝ ∞ (fun v : Euc d => ‖v‖ ^ (-criticalS d)) w :=
    (contDiffAt_norm ℝ hw).rpow_const_of_ne (norm_pos_iff.2 hw).ne'
  exact h1.fderiv_right (by simp)

theorem r26t8a_p17_h_contDiffOn (hd : 2 ≤ d) {A : ℝ} {k : ℕ} {f : Euc d → ℝ} (hf : TestBound k A f) :
    ContDiffOn ℝ ∞ (Function.uncurry (hSource f)) {p : Euc d × Euc d | p.1 ≠ p.2} := by
  intro p hp
  have hne : p.1 - p.2 ≠ 0 := sub_ne_zero.2 hp
  have hφ := r26t8a_p17_grad_contDiff hf.1
  have h1 : ContDiffAt ℝ ∞ (fun q : Euc d × Euc d => fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d)) (q.1 - q.2)) p :=
    ((r26t8a_p17_g_contDiffAt hd hne).comp p (contDiff_fst.sub contDiff_snd).contDiffAt)
  have h2 : ContDiffAt ℝ ∞ (fun q : Euc d × Euc d => gradient f q.1 - gradient f q.2) p :=
    ((hφ.comp contDiff_fst).sub (hφ.comp contDiff_snd)).contDiffAt
  have h3 := h1.clm_apply h2
  have e : Function.uncurry (hSource f) = fun q : Euc d × Euc d =>
      fderiv ℝ (fun v : Euc d => ‖v‖ ^ (-criticalS d)) (q.1 - q.2) (gradient f q.1 - gradient f q.2) := by
    funext q; exact r26t8a_p17_h_eq hd f q.1 q.2
  rw [e]
  exact h3.contDiffWithinAt

end HRS.MS.R26T8A
