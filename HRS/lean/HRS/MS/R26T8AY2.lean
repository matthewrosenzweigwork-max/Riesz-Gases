import HRS.MS.R26T8AY1m
import HRS.MS.R26T8AP11f8
import HRS.MS.R26T8AZ5c

/-!
# S8.2 T8A Y2: the `x`-derivative of the local Riesz potential of a supported singular source
`r26t8a_Y2_deriv`: `P` supported in `|x-y| ≤ 1/2`, `C^1` off the diagonal, `|P(y+v,y)| ≤ c0`, `‖D_v P(y+v,y)‖ ≤ c1 |v|^{-1}`; for `0 < |x-y| < 1`:
`x' ↦ localRiesz α chi P x' y` has derivative `L` at `x` with `L e_i = localRiesz α chi (dx_i P) x y`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Y2_eq (hd : 2 ≤ d) (α : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {P : Euc d → Euc d → ℝ}
    (y : Euc d) (hsupp : ∀ v : Euc d, 1 / 2 < ‖v‖ → P (y + v) y = 0) {x : Euc d} (hx : ‖x - y‖ ≤ 1) :
    r26t8a_localRiesz α chi P x y = ∫ v, r26t8a_Y0_rK d α (x - y - v) * P (y + v) y := by
  unfold r26t8a_localRiesz
  rw [hchi.2.2.2.1 _ hx, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  by_cases hv : ‖v‖ ≤ 1
  · simp only [r26t8a_Y0_rK, hchi.2.2.2.1 v hv, mul_one]
  · simp only [r26t8a_Y0_rK, hsupp v (by linarith [not_le.1 hv]), mul_zero]

set_option maxHeartbeats 3200000 in
theorem r26t8a_Y2_deriv (hd : 2 ≤ d) {α : ℝ} (hα : 0 < α) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    {P : Euc d → Euc d → ℝ}
    (hP1 : ContDiffOn ℝ 1 (Function.uncurry P) {p : Euc d × Euc d | p.1 ≠ p.2}) (y : Euc d)
    (hsupp : ∀ v : Euc d, 1 / 2 < ‖v‖ → P (y + v) y = 0) {c0 c1 : ℝ}
    (hc0 : ∀ v : Euc d, v ≠ 0 → |P (y + v) y| ≤ c0)
    (hc1 : ∀ v : Euc d, v ≠ 0 → ‖fderiv ℝ (fun v => P (y + v) y) v‖ ≤ c1 * ‖v‖ ^ (-(1 : ℝ)))
    {x : Euc d} (hxy : x ≠ y) (hx1 : ‖x - y‖ < 1) :
    HasFDerivAt (fun x' => r26t8a_localRiesz α chi P x' y)
      (∫ v, r26t8a_Y0_rK d α (x - y - v) • fderiv ℝ (fun v => P (y + v) y) v) x ∧
    ∀ i : Fin d, (∫ v, r26t8a_Y0_rK d α (x - y - v) • fderiv ℝ (fun v => P (y + v) y) v) (r26t8a_e d i) =
      r26t8a_localRiesz α chi (r26t8a_dx i P) x y := by
  haveI := r26t8a_nontrivial hd
  set G : Euc d → ℝ := fun v => P (y + v) y with hG
  have hG1 : ContDiffOn ℝ 1 G {0}ᶜ := by
    have h : ContDiff ℝ 1 (fun v : Euc d => (y + v, y)) := (contDiff_const.add contDiff_id).prodMk contDiff_const
    refine hP1.comp h.contDiffOn (fun v hv => ?_)
    intro h0
    apply hv
    have : y + v = y := h0
    simpa using this
  have hGc : ∀ w, 2 < ‖w‖ → G w = 0 := fun w hw => hsupp w (by linarith)
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hmain := r26t8a_Y1_conv_hasFDeriv hd hα hchi hG1 hGc hc0 hc1 one_pos
    (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith) hz
  have hsub : HasFDerivAt (fun x' : Euc d => x' - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
    (hasFDerivAt_id x).sub_const y
  have hcomp := hmain.comp x hsub
  have hev : (fun x' => r26t8a_localRiesz α chi P x' y) =ᶠ[𝓝 x]
      (fun z' => ∫ v, r26t8a_Y0_rK d α (z' - v) * G v) ∘ (fun x' => x' - y) := by
    filter_upwards [(isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).mem_nhds hx1]
      with x' hx'
    exact r26t8a_Y2_eq hd α hchi y hsupp hx'.le
  refine ⟨?_, fun i => ?_⟩
  · have := hcomp.congr_of_eventuallyEq hev
    simpa using this
  · have hint := r26t8a_Y1_int hd hα hG1 hGc hc1 one_pos
      (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
          linarith) hz
    rw [ContinuousLinearMap.integral_apply hint]
    have hsupp' : ∀ v : Euc d, 1 / 2 < ‖v‖ → r26t8a_dx i P (y + v) y = 0 := by
      intro v hv
      have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; linarith
      have : (fun x' => P x' y) =ᶠ[𝓝 (y + v)] fun _ => 0 := by
        have hopen : IsOpen {x' : Euc d | 1 / 2 < ‖x' - y‖} :=
          isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
        filter_upwards [hopen.mem_nhds (by simpa using hv)] with x' hx'
        have := hsupp (x' - y) hx'
        simpa using this
      unfold r26t8a_dx
      rw [this.fderiv_eq]
      simp
    rw [r26t8a_Y2_eq hd α hchi y hsupp' hx1.le]
    refine integral_congr_ae ?_
    filter_upwards [r26t8a_ae_ne_zero hd] with v hv
    have hdiff : DifferentiableAt ℝ (fun x' => P x' y) (y + v) := by
      have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
      have h1 : DifferentiableAt ℝ (Function.uncurry P) (y + v, y) :=
        (hP1.contDiffAt (hopen.mem_nhds (by simpa using hv))).differentiableAt (by norm_num)
      have h2 : DifferentiableAt ℝ (fun x' : Euc d => (x', y)) (y + v) :=
        differentiableAt_id.prodMk (differentiableAt_const y)
      exact DifferentiableAt.comp (g := Function.uncurry P) (f := fun x' : Euc d => (x', y)) (y + v) h1 h2
    have hfd : fderiv ℝ G v = fderiv ℝ (fun x' => P x' y) (y + v) := by
      rw [show G = (fun x' => P x' y) ∘ (fun v => y + v) from rfl]
      have := hdiff.hasFDerivAt.comp v ((hasFDerivAt_id v).const_add y)
      rw [this.fderiv]; simp
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hfd]
    rfl

end HRS.MS.R26T8A
