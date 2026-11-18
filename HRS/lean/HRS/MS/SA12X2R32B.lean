import HRS.MS.SA12X2R32A

/-!
# S.A.12 R32 (SA12X2), part B: uniform-in-scale L1 bound on the derivative of the spill kernel

For `0 < r ≤ 1`: `∫_{|h| ≤ R₀} |∂_w Kf_r(h)| dh ≤ C (1 + R₀) r^(-(s+2-d))`, with `C` independent of `r`, `w`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.MH.AdjointRdP

variable {d : ℕ}

/-- The missing estimate: uniform-in-scale L1 bound of the ball-restricted derivative of `Kf_r`. -/
theorem sa12x2_kf_L1 {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) < s + 2) (R₀ : ℝ) (hR₀ : 0 ≤ R₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ w : Euc d, ‖w‖ ≤ 1 →
      ∫ h, (closedBall (0 : Euc d) R₀).indicator (fun h => |fderiv ℝ (r3Kf d s r) h w|) h
        ≤ C * r ^ (-(s + 2 - d)) := by
  obtain ⟨CF, hCF0, hCF⟩ := sa12x2_F1_grad_bound (d := d) hs0
  have hint : Integrable (fun k : Euc d => (1 + ‖k‖) ^ (-(s + 2))) (volume : Measure (Euc d)) :=
    integrable_one_add_norm (μ := (volume : Measure (Euc d))) (by simpa [finrank_euclideanSpace_fin] using hs2)
  set I : ℝ := ∫ k : Euc d, (1 + ‖k‖) ^ (-(s + 2)) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun k => by positivity
  refine ⟨CF * I * (1 + R₀), mul_nonneg (mul_nonneg hCF0 hI0) (by linarith), ?_⟩
  intro r hr hr1 w hw
  have hCw : 0 ≤ CF * ‖w‖ := mul_nonneg hCF0 (norm_nonneg _)
  -- derivative identity for `Kf_r(h) = r^(-s) F1(r⁻¹ h)`
  have hD : ∀ h : Euc d, fderiv ℝ (r3Kf d s r) h w =
      r ^ (-s) * (r⁻¹ * fderiv ℝ (r3F1 d s) (r⁻¹ • h) w) := by
    intro h
    have hfun : r3Kf d s r = fun y => r ^ (-s) * r3F1 d s (r⁻¹ • y) :=
      funext fun y => r3Kf_eq s hr y
    have hG : HasFDerivAt (r3F1 d s) (fderiv ℝ (r3F1 d s) (r⁻¹ • h)) (r⁻¹ • h) :=
      ((r3F1_contDiff (d := d) (s := s)).differentiable (by simp) _).hasFDerivAt
    have hL : HasFDerivAt (fun y : Euc d => r⁻¹ • y)
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) h :=
      (hasFDerivAt_id h).const_smul r⁻¹
    have hc : HasFDerivAt (fun y : Euc d => r ^ (-s) * r3F1 d s (r⁻¹ • y))
        (r ^ (-s) • ((fderiv ℝ (r3F1 d s) (r⁻¹ • h)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Euc d)))) h :=
      (hG.comp h hL).const_mul (r ^ (-s))
    rw [hfun, hc.fderiv]
    simp [ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  -- pointwise majorant
  have hpt : ∀ h : Euc d,
      (closedBall (0 : Euc d) R₀).indicator (fun h => |fderiv ℝ (r3Kf d s r) h w|) h ≤
        r ^ (-s - 1) * (CF * ‖w‖ * (1 + R₀ / r)) * (1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) := by
    intro h
    by_cases hh : h ∈ closedBall (0 : Euc d) R₀
    · rw [indicator_of_mem hh, hD h, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr.le _),
        abs_of_pos (inv_pos.2 hr)]
      have hk : ‖r⁻¹ • h‖ ≤ R₀ / r := by
        rw [mem_closedBall_zero_iff] at hh
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hh (inv_nonneg.2 hr.le)
      have hb := hCF (r⁻¹ • h) w
      have hsplit : (1 + ‖r⁻¹ • h‖) ^ (-(s + 1)) =
          (1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) * (1 + ‖r⁻¹ • h‖) := by
        rw [← Real.rpow_add_one (by positivity)]
        congr 1; ring
      have h1 : (1 + ‖r⁻¹ • h‖) ≤ 1 + R₀ / r := by linarith
      have hgnn : 0 ≤ (1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) := by positivity
      calc r ^ (-s) * (r⁻¹ * |fderiv ℝ (r3F1 d s) (r⁻¹ • h) w|)
          ≤ r ^ (-s) * (r⁻¹ * (CF * ‖w‖ * (1 + ‖r⁻¹ • h‖) ^ (-(s + 1)))) := by
            gcongr
        _ = r ^ (-s) * r⁻¹ * (CF * ‖w‖ * ((1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) * (1 + ‖r⁻¹ • h‖))) := by
            rw [hsplit]; ring
        _ ≤ r ^ (-s) * r⁻¹ * (CF * ‖w‖ * ((1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) * (1 + R₀ / r))) := by
            gcongr
        _ = r ^ (-s - 1) * (CF * ‖w‖ * (1 + R₀ / r)) * (1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) := by
            rw [Real.rpow_sub_one hr.ne']; ring
    · rw [indicator_of_notMem hh]
      have : 0 ≤ R₀ / r := div_nonneg hR₀ hr.le
      have : 0 ≤ (1 + R₀ / r) := by linarith
      positivity
  -- integrability of the majorant
  have hgi : Integrable (fun h : Euc d => (1 + ‖r⁻¹ • h‖) ^ (-(s + 2))) (volume : Measure (Euc d)) :=
    (integrable_comp_smul_iff (volume : Measure (Euc d))
      (fun k : Euc d => (1 + ‖k‖) ^ (-(s + 2))) (inv_ne_zero hr.ne')).2 hint
  -- change of variables
  have hcv : ∫ h : Euc d, (1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) = r ^ d * I := by
    have := MeasureTheory.Measure.integral_comp_inv_smul (μ := (volume : Measure (Euc d)))
      (fun k : Euc d => (1 + ‖k‖) ^ (-(s + 2))) r
    rw [finrank_euclideanSpace_fin] at this
    rw [this, abs_of_pos (pow_pos hr d)]
    rfl
  have e1 : r ^ (-s - 1) * r ^ d = r ^ (-(s + 2 - d)) * r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, ← Real.rpow_add_one hr.ne']
    congr 1; push_cast; ring
  have e2 : r * (1 + R₀ / r) = r + R₀ := by field_simp
  have hTp : 0 ≤ r ^ (-(s + 2 - d)) := Real.rpow_nonneg hr.le _
  calc ∫ h, (closedBall (0 : Euc d) R₀).indicator (fun h => |fderiv ℝ (r3Kf d s r) h w|) h
      ≤ ∫ h : Euc d, r ^ (-s - 1) * (CF * ‖w‖ * (1 + R₀ / r)) * (1 + ‖r⁻¹ • h‖) ^ (-(s + 2)) :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun h => indicator_nonneg (fun _ _ => abs_nonneg _) h)
          (hgi.const_mul _) (Eventually.of_forall hpt)
    _ = r ^ (-s - 1) * (CF * ‖w‖ * (1 + R₀ / r)) * (r ^ d * I) := by
        rw [integral_const_mul, hcv]
    _ = (CF * ‖w‖ * I) * r ^ (-(s + 2 - d)) * (r + R₀) := by
        calc r ^ (-s - 1) * (CF * ‖w‖ * (1 + R₀ / r)) * (r ^ d * I)
            = (CF * ‖w‖ * I) * (r ^ (-s - 1) * r ^ d) * (1 + R₀ / r) := by ring
          _ = (CF * ‖w‖ * I) * (r ^ (-(s + 2 - d)) * r) * (1 + R₀ / r) := by rw [e1]
          _ = (CF * ‖w‖ * I) * r ^ (-(s + 2 - d)) * (r * (1 + R₀ / r)) := by ring
          _ = (CF * ‖w‖ * I) * r ^ (-(s + 2 - d)) * (r + R₀) := by rw [e2]
    _ ≤ CF * I * (1 + R₀) * r ^ (-(s + 2 - d)) := by
        have hw' : CF * ‖w‖ * I ≤ CF * I := by
          calc CF * ‖w‖ * I = (CF * I) * ‖w‖ := by ring
            _ ≤ (CF * I) * 1 := mul_le_mul_of_nonneg_left hw (mul_nonneg hCF0 hI0)
            _ = CF * I := mul_one _
        have hTI : 0 ≤ CF * ‖w‖ * I := mul_nonneg hCw hI0
        have hR' : r + R₀ ≤ 1 + R₀ := by linarith
        have hRn : 0 ≤ r + R₀ := by linarith
        calc (CF * ‖w‖ * I) * r ^ (-(s + 2 - d)) * (r + R₀)
            ≤ (CF * I) * r ^ (-(s + 2 - d)) * (1 + R₀) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hw' hTp) hR' hRn
              exact mul_nonneg (mul_nonneg hCF0 hI0) hTp
          _ = CF * I * (1 + R₀) * r ^ (-(s + 2 - d)) := by ring

end HRS.MH.AdjointRd.Phase2SA12
