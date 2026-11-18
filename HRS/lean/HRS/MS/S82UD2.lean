import HRS.MS.S82UD1

/-!
# S8.2 A01 (S82U): grouped form and mean of `J` for `ψ_y = ∇_1 Q(·,y)`; integrability of the pieces
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

/-- `μ`-integrability of the grouped edge envelope. -/
theorem u_edge_int {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} {Gc c : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hQ : PairCorrector a beta rho M A f Q) (hG : 0 ≤ Gc) (hc : 0 < c)
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho)
    {x y : Euc d} (hxy : x ≠ y) :
    Integrable (fun z => ‖rieszKernelGrad d (criticalS d) (x - z)‖ * ‖s82p2_gt Q z y - s82p2_gt Q x y‖)
      (HRS.Whole.withDensityReal rho) := by
  set Ce := HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) with hCe
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hCe0 : 0 ≤ Ce := mul_nonneg (s82t_sigma_nonneg _ hs0) (by positivity)
  have hint := u_int_triple hd (by linarith : 0 ≤ 2 * M) hG hc hρ hρG hxy
  have hb := hint.const_mul (Ce * (A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M))))
  have hGm : Measurable (rieszKernelGrad d (criticalS d)) :=
    HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hgm := u_gt_section_measurable Q y
  refine Integrable.mono' hb ((hGm.comp (measurable_const.sub measurable_id)).norm.mul
    (hgm.sub measurable_const).norm).aestronglyMeasurable ?_
  have hmu : ∀ᵐ z ∂(HRS.Whole.withDensityReal rho), z ≠ y := s82t_mu_ae_ne hd rho y
  filter_upwards [hmu] with z hz
  have hnn : 0 ≤ ‖rieszKernelGrad d (criticalS d) (x - z)‖ * ‖s82p2_gt Q z y - s82p2_gt Q x y‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  by_cases hxz : x = z
  · subst hxz; simp only [sub_self, norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hCe0 (mul_nonneg hA (mul_nonneg (u_jb_rpow_pos _ _).le (u_jb_rpow_pos _ _).le)))
      (mul_nonneg (u_jb_rpow_pos _ _).le (by linarith [u_tp_ge x y x |>.1, u_pole_pos x y]))
  · have hedge := u_edge_norm hd hM hA hQ (u := x) (v := z) (w := y) hxz hxy hz
    rw [norm_sub_rev (s82p2_gt Q z y) (s82p2_gt Q x y)]
    refine hedge.trans ?_
    obtain ⟨t1, -, -⟩ := u_tp_sub x y z
    have hperm := (u_uW_perm M x y z).1
    rw [hperm, u_pole_symm z y]
    unfold uW
    have hj := (u_jb_rpow_pos (2 * M) z).le
    have hjx := (u_jb_rpow_pos (2 * M) x).le
    have hjy := (u_jb_rpow_pos (2 * M) y).le
    have e : Ce * (A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M) * jbracket z ^ (2 * M)) *
        (pole x z * (pole x y + pole y z))) =
        (Ce * (A * (jbracket x ^ (2 * M) * jbracket y ^ (2 * M)))) *
          (jbracket z ^ (2 * M) * (pole x z * (pole x y + pole y z))) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCe0 (mul_nonneg hA (mul_nonneg hjx hjy)))
    exact mul_le_mul_of_nonneg_left t1 hj

end HRS.MS.S82U
