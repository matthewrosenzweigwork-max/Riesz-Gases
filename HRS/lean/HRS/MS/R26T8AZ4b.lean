import HRS.MS.R26T8AZ3i
import HRS.MS.R26T8AZ4a
import HRS.MS.R26T8AN4

/-!
# S8.2 T8A Z4b: the derivative of the Newton potential of a supported singular source (no extra boundary term)
`r26t8a_Z4b_deriv`: `P` supported in `|x-y| ≤ 1/2`, `C^1` off the diagonal, with `|Ψ| ≤ c0`, `‖DΨ(w)‖ ≤ c1 |w|^{-s1}` (`Ψ = midPair P X`),
`0 < |z| < 1`: the slice `w ↦ midPair (rawNewton P) X w` has derivative `L` at `z` with `L e = midPair (rawNewton (pdir (0,e) P)) X z`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z4b_mid_eq (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {P : Euc d → Euc d → ℝ}
    (X : Euc d) (hsupp : ∀ w : Euc d, 1 / 2 < ‖w‖ → midPair P X w = 0) {w : Euc d} (hw : ‖w‖ ≤ 1) :
    midPair (rawNewton nu chi P) X w = ∫ v, newtonKernel d nu (w - v) * midPair P X v := by
  rw [r26t8a_N4_mid_eq, hchi.2.2.2.1 w hw, one_mul]
  have e : ∀ v : Euc d, chi v * midPair P X v = midPair P X v := fun v => by
    by_cases hv : ‖v‖ ≤ 1
    · rw [hchi.2.2.2.1 v hv, one_mul]
    · rw [hsupp v (by linarith [not_le.1 hv]), mul_zero]
  have h := r26t8a_Z3_swap (newtonKernel d nu) (fun v => chi v * midPair P X v) w
  simp only [smul_eq_mul] at h
  rw [h]
  exact integral_congr_ae (Eventually.of_forall fun v => by simp only [e])

set_option maxHeartbeats 3200000 in
theorem r26t8a_Z4b_deriv (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {P : Euc d → Euc d → ℝ}
    (hP1 : ContDiffOn ℝ 1 (Function.uncurry P) {p : Euc d × Euc d | p.1 ≠ p.2}) (X : Euc d)
    (hsupp : ∀ w : Euc d, 1 / 2 < ‖w‖ → midPair P X w = 0) {c0 c1 s1 : ℝ}
    (hc0 : ∀ w, w ≠ 0 → |midPair P X w| ≤ c0)
    (hc1 : ∀ w, w ≠ 0 → ‖fderiv ℝ (fun w => midPair P X w) w‖ ≤ c1 * ‖w‖ ^ (-s1)) (hs1 : 0 < s1) (hs1d : s1 < d)
    {z : Euc d} (hz : z ≠ 0) (hz1 : ‖z‖ < 1) :
    HasFDerivAt (fun w => midPair (rawNewton nu chi P) X w)
      (∫ v, newtonKernel d nu (z - v) • fderiv ℝ (fun w => midPair P X w) v) z ∧
    ∀ e : Euc d, (∫ v, newtonKernel d nu (z - v) • fderiv ℝ (fun w => midPair P X w) v) e =
      midPair (rawNewton nu chi (r26t8a_pdir (0, e) P)) X z := by
  haveI := r26t8a_nontrivial hd
  set Ψ : Euc d → ℝ := fun w => midPair P X w with hΨ
  have hΨ1 : ContDiffOn ℝ 1 Ψ {0}ᶜ := by
    have h1 := r26t8a_midPair_contDiffOn hP1
    have h2 : ContDiffOn ℝ 1 (fun w : Euc d => (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) (X, w)) {0}ᶜ :=
      h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun w hw => hw)
    exact h2
  have hΨc : ∀ w, 2 < ‖w‖ → Ψ w = 0 := fun w hw => hsupp w (by linarith)
  have hmain := r26t8a_Z3_conv_hasFDeriv hd nu hchi hΨ1 hΨc hc0 hc1 hs1 hs1d hz
  have hev : (fun w => midPair (rawNewton nu chi P) X w) =ᶠ[𝓝 z] fun z' => ∫ v, newtonKernel d nu (z' - v) * Ψ v := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz1] with w hw
    exact r26t8a_Z4b_mid_eq hd nu hchi X hsupp hw.le
  refine ⟨hmain.congr_of_eventuallyEq hev, fun e => ?_⟩
  have hint := r26t8a_Z3i_int hd nu hΨ1 hΨc hc1 hs1 hs1d hz
  rw [ContinuousLinearMap.integral_apply hint]
  -- the right side
  have hsupp' : ∀ w : Euc d, 1 / 2 < ‖w‖ → midPair (r26t8a_pdir (0, e) P) X w = 0 := by
    intro w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw; linarith
    rw [r26t8a_Z4a_slice hP1 X w hw0 e]
    have : Ψ =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with u hu using hsupp u hu
    have h0 : fderiv ℝ Ψ w = 0 := by rw [this.fderiv_eq]; exact fderiv_const_apply 0
    simp only [hΨ] at h0
    rw [h0]; rfl
  rw [r26t8a_Z4b_mid_eq hd nu hchi X hsupp' hz1.le]
  refine integral_congr_ae ?_
  filter_upwards [r26t8a_ae_ne_zero hd] with v hv
  rw [r26t8a_Z4a_slice hP1 X v hv e]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

end HRS.MS.R26T8A
