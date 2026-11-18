import HRS.MS.R26T8AP22b

/-!
# S8.2 local Newton layer, packet T8A.P22 (part c): size of the leading inverse and of its gradient
`r26t8a_p22_L_bounds`: `|L_B z| <= C ‖B‖ (|z|^(2-s) + [d=4](1+|log|z||))` and `‖∇ L_B z‖ <= C ‖B‖ |z|^(1-s)` for `0 < |z| <= 2`,
`C` independent of `B` (homogeneity reduces to the unit sphere; uniformity in `B` is `r26t8a_p22_unif`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_hom_uniform (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, ∀ w : Euc d, w ≠ 0 →
      s82n_leadingInverse nu B (t • w) = t ^ (2 - s82n_critS d) * s82n_leadingInverse nu B w + c := by
  by_cases hd4 : d = 4
  · refine ⟨(∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) / d * Real.log t / (4 * nu),
      fun w hw => ?_⟩
    have hs : s82n_critS d = 2 := by unfold s82n_critS; rw [hd4]; norm_num
    rw [r26t8a_p22_L_hom_four nu B hd4 hw ht, hs]
    norm_num
  · exact ⟨0, fun w hw => by rw [r26t8a_p22_L_hom_ne nu B hd4 hw ht, add_zero]⟩

theorem r26t8a_p22_fderiv_scale (nu : ℝ) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) {z : Euc d} (hz : z ≠ 0) {t : ℝ}
    (ht : 0 < t) :
    fderiv ℝ (s82n_leadingInverse nu B) (t • z) =
      t ^ (1 - s82n_critS d) • fderiv ℝ (s82n_leadingInverse nu B) z := by
  obtain ⟨c, hc⟩ := r26t8a_p22_hom_uniform nu B ht
  have htz : t • z ≠ 0 := smul_ne_zero ht.ne' hz
  have hD1 : DifferentiableAt ℝ (s82n_leadingInverse nu B) (t • z) :=
    ((r26t8a_p22_L_contDiffAt nu B htz).differentiableAt (by simp))
  have hD2 : DifferentiableAt ℝ (s82n_leadingInverse nu B) z :=
    ((r26t8a_p22_L_contDiffAt nu B hz).differentiableAt (by simp))
  have hcomp : fderiv ℝ (fun w => s82n_leadingInverse nu B (t • w)) z =
      t • fderiv ℝ (s82n_leadingInverse nu B) (t • z) := by
    have hh : HasFDerivAt (fun w : Euc d => t • w) (t • ContinuousLinearMap.id ℝ (Euc d)) z :=
      (hasFDerivAt_id z).const_smul t
    have h := (hD1.hasFDerivAt.comp z hh).fderiv
    rw [show (fun w => s82n_leadingInverse nu B (t • w)) = s82n_leadingInverse nu B ∘ (fun w => t • w) from rfl, h]
    ext v
    simp
  have hev : (fun w => s82n_leadingInverse nu B (t • w)) =ᶠ[𝓝 z]
      fun w => t ^ (2 - s82n_critS d) * s82n_leadingInverse nu B w + c := by
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw using hc w hw
  have hrhs : fderiv ℝ (fun w => t ^ (2 - s82n_critS d) * s82n_leadingInverse nu B w + c) z =
      t ^ (2 - s82n_critS d) • fderiv ℝ (s82n_leadingInverse nu B) z := by
    rw [fderiv_add_const, fderiv_const_mul hD2]
  rw [hev.fderiv_eq, hrhs] at hcomp
  have h2 : t ^ (2 - s82n_critS d) = t * t ^ (1 - s82n_critS d) := by
    have : (2 : ℝ) - s82n_critS d = 1 + (1 - s82n_critS d) := by ring
    rw [this, Real.rpow_add ht, Real.rpow_one]
  rw [h2, mul_smul] at hcomp
  calc fderiv ℝ (s82n_leadingInverse nu B) (t • z)
      = t⁻¹ • (t • fderiv ℝ (s82n_leadingInverse nu B) (t • z)) := by
        rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = t⁻¹ • (t • (t ^ (1 - s82n_critS d) • fderiv ℝ (s82n_leadingInverse nu B) z)) := by rw [hcomp]
    _ = t ^ (1 - s82n_critS d) • fderiv ℝ (s82n_leadingInverse nu B) z := by
        rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]

end HRS.MS.R26T8A
