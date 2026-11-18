import HRS.MS.R26T8AP22c

/-!
# S8.2 local Newton layer, packet T8A.P22 (part d): bounds for the leading inverse
`r26t8a_p22_L_bounds`: for `z != 0`, `|L_B z| <= C ‖B‖ (|z|^(2-s) + [d=4] |log|z||)` and `‖fderiv L_B z‖ <= C ‖B‖ |z|^(1-s)`,
with `C` depending only on `d, nu`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p22_h0_le (hd : 2 ≤ d) (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) :
    |(∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) / d| ≤ ‖B‖ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0]
  calc |∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin d, |B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ‖B‖ := Finset.sum_le_sum fun i _ => by
        have h := B.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
        simpa [EuclideanSpace.norm_single] using h
    _ = ‖B‖ * d := by simp [mul_comm]

theorem r26t8a_p22_sphere_ne : ∀ om ∈ sphere (0 : Euc d) 1, om ≠ 0 := fun om hom h => by
  rw [h] at hom; simp at hom

set_option maxHeartbeats 1600000 in
theorem r26t8a_p22_sphere_value (nu : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), ∀ om ∈ sphere (0 : Euc d) 1,
      ‖s82n_leadingInverse nu B om‖ ≤ C * ‖B‖ :=
  r26t8a_p22_unif (isCompact_sphere _ _)
    (fun (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) om => s82n_leadingInverse nu B om)
    (fun B1 B2 x _ => r26t8a_p22_L_add nu B1 B2 x) (fun c B x _ => by simpa using r26t8a_p22_L_smul nu c B x)
    (fun B => fun om hom => ((r26t8a_p22_L_contDiffAt nu B (r26t8a_p22_sphere_ne om hom)).continuousAt).continuousWithinAt)

set_option maxHeartbeats 1600000 in
theorem r26t8a_p22_sphere_grad (nu : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ), ∀ om ∈ sphere (0 : Euc d) 1,
      ‖fderiv ℝ (s82n_leadingInverse nu B) om‖ ≤ C * ‖B‖ := by
  refine r26t8a_p22_unif (isCompact_sphere _ _)
    (fun (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) om => fderiv ℝ (s82n_leadingInverse nu B) om)
    (fun B1 B2 x hx => ?_) (fun c B x hx => ?_) (fun B => fun om hom => ?_)
  · have e : s82n_leadingInverse nu (B1 + B2) = s82n_leadingInverse nu B1 + s82n_leadingInverse nu B2 :=
      funext fun z => r26t8a_p22_L_add nu B1 B2 z
    show fderiv ℝ (s82n_leadingInverse nu (B1 + B2)) x = fderiv ℝ (s82n_leadingInverse nu B1) x +
      fderiv ℝ (s82n_leadingInverse nu B2) x
    rw [e]
    exact fderiv_add ((r26t8a_p22_L_contDiffAt nu B1 (r26t8a_p22_sphere_ne x hx)).differentiableAt (by simp))
      ((r26t8a_p22_L_contDiffAt nu B2 (r26t8a_p22_sphere_ne x hx)).differentiableAt (by simp))
  · have e : s82n_leadingInverse nu (c • B) = fun z => c * s82n_leadingInverse nu B z :=
      funext fun z => r26t8a_p22_L_smul nu c B z
    show fderiv ℝ (s82n_leadingInverse nu (c • B)) x = c • fderiv ℝ (s82n_leadingInverse nu B) x
    rw [e]
    exact fderiv_const_mul ((r26t8a_p22_L_contDiffAt nu B (r26t8a_p22_sphere_ne x hx)).differentiableAt (by simp)) c
  · have := (r26t8a_p22_L_contDiffAt nu B (r26t8a_p22_sphere_ne om hom)).fderiv_right (m := 0) (by norm_num)
    exact this.continuousAt.continuousWithinAt

theorem r26t8a_p22_L_bounds (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ) (z : Euc d), z ≠ 0 →
      |s82n_leadingInverse nu B z| ≤ C * ‖B‖ * (‖z‖ ^ (2 - s82n_critS d) +
        (if d = 4 then |Real.log ‖z‖| else 0)) ∧
      ‖fderiv ℝ (s82n_leadingInverse nu B) z‖ ≤ C * ‖B‖ * ‖z‖ ^ (1 - s82n_critS d) := by
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_p22_sphere_value (d := d) nu
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_p22_sphere_grad (d := d) nu
  have hne := r26t8a_p22_sphere_ne (d := d)
  refine ⟨C1 + C2 + 1 / (4 * nu), by positivity, fun B z hz => ?_⟩
  have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
  set t : ℝ := ‖z‖ with htdef
  set om : Euc d := t⁻¹ • z with homdef
  have hom : om ∈ sphere (0 : Euc d) 1 := by
    simp only [mem_sphere_iff_norm, sub_zero, homdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht]
    field_simp
    first | done | exact htdef.symm
  have hz' : z = t • om := by
    simp only [homdef, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hnB : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  have hC : 0 ≤ C1 + C2 + 1 / (4 * nu) := by positivity
  constructor
  · have h1 := (Real.norm_eq_abs _ ▸ hC1 B om hom : |s82n_leadingInverse nu B om| ≤ C1 * ‖B‖)
    by_cases hd4 : d = 4
    · have hs : s82n_critS d = 2 := by unfold s82n_critS; rw [hd4]; norm_num
      have hL := r26t8a_p22_L_hom_four nu B hd4 (hne om hom) ht
      rw [← hz'] at hL
      have h0 := r26t8a_p22_h0_le hd B
      have hlog : |(∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) / d *
          Real.log t / (4 * nu)| ≤ ‖B‖ * |Real.log t| / (4 * nu) := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 4 * nu), div_le_div_iff_of_pos_right (by positivity)]
        exact mul_le_mul_of_nonneg_right h0 (abs_nonneg _)
      rw [hL, if_pos hd4, hs, sub_self, Real.rpow_zero]
      calc |s82n_leadingInverse nu B om + (∑ i : Fin d, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) / d *
            Real.log t / (4 * nu)| ≤ |s82n_leadingInverse nu B om| + ‖B‖ * |Real.log t| / (4 * nu) :=
            (abs_add_le _ _).trans (add_le_add le_rfl hlog)
        _ ≤ C1 * ‖B‖ + ‖B‖ * |Real.log t| / (4 * nu) := by linarith
        _ ≤ (C1 + C2 + 1 / (4 * nu)) * ‖B‖ * (1 + |Real.log t|) := by
            have h4 : 0 ≤ C2 * ‖B‖ * (1 + |Real.log t|) := by positivity
            have h5 : 0 ≤ C1 * ‖B‖ * |Real.log t| := by positivity
            have : ‖B‖ * |Real.log t| / (4 * nu) = 1 / (4 * nu) * ‖B‖ * |Real.log t| := by ring
            rw [this]
            nlinarith [mul_nonneg hnB (abs_nonneg (Real.log t)), one_div_nonneg.2 (by positivity : 0 ≤ 4 * nu)]
    · rw [if_neg hd4, add_zero]
      have hL := r26t8a_p22_L_hom_ne nu B hd4 (hne om hom) ht
      rw [← hz'] at hL
      rw [hL, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
      have hp : 0 ≤ t ^ (2 - s82n_critS d) := Real.rpow_nonneg ht.le _
      calc t ^ (2 - s82n_critS d) * |s82n_leadingInverse nu B om| ≤ t ^ (2 - s82n_critS d) * (C1 * ‖B‖) :=
            mul_le_mul_of_nonneg_left h1 hp
        _ ≤ (C1 + C2 + 1 / (4 * nu)) * ‖B‖ * t ^ (2 - s82n_critS d) := by
            have : 0 ≤ (C2 + 1 / (4 * nu)) * ‖B‖ * t ^ (2 - s82n_critS d) := by positivity
            nlinarith
  · have h2 := hC2 B om hom
    have hsc := r26t8a_p22_fderiv_scale nu B (hne om hom) ht
    rw [← hz'] at hsc
    rw [hsc, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    have hp : 0 ≤ t ^ (1 - s82n_critS d) := Real.rpow_nonneg ht.le _
    calc t ^ (1 - s82n_critS d) * ‖fderiv ℝ (s82n_leadingInverse nu B) om‖ ≤ t ^ (1 - s82n_critS d) * (C2 * ‖B‖) :=
          mul_le_mul_of_nonneg_left h2 hp
      _ ≤ (C1 + C2 + 1 / (4 * nu)) * ‖B‖ * t ^ (1 - s82n_critS d) := by
          have : 0 ≤ (C1 + 1 / (4 * nu)) * ‖B‖ * t ^ (1 - s82n_critS d) := by positivity
          nlinarith

end HRS.MS.R26T8A
