import HRS.MS.R26T8AR3d

/-!
# S8.2 T8A R3e: nested jets of `Φ(Y,w) = LI(D²f(Y))(w) + S0(D²f(Y))(w)` of order `≤ 2`
`r26t8a_R3_nest_Phi`: for `0 < |z| ≤ 1`, `q ≤ 2`:
`‖nest p q Φ X z‖ ≤ C ‖D^p (D²f) X‖ (1 + |z|^(-((s-2)+q)) + [q=0][d=4] |log |z||)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_R3_nest_Phi (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euc d → ℝ), ContDiff ℝ ∞ f → ∀ (X z : Euc d), z ≠ 0 → ‖z‖ ≤ 1 →
      ∀ (p q : ℕ), q ≤ 2 →
      ‖r26t8a_nest p q (fun Yw : Euc d × Euc d =>
          s82n_leadingInverse nu (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2 +
            r26t8a_p22_S0 nu chi (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2) X z‖ ≤
        C * ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ *
          (1 + ‖z‖ ^ (-((s82n_critS d - 2) + (q : ℝ))) +
            if q = 0 then (if d = 4 then |Real.log ‖z‖| else 0) else 0) := by
  obtain ⟨CL, hCL0, hCL⟩ := r26t8a_p22_L_bounds hd nu hnu
  obtain ⟨CH, hCH0, hCH⟩ := r26t8a_R3_L_hess hd nu
  obtain ⟨C0, hC00, hC0⟩ := r26t8a_p22_S0_jets hd nu hchi 0
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_p22_S0_jets hd nu hchi 1
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_p22_S0_jets hd nu hchi 2
  refine ⟨CL + CH + C0 + C1 + C2, by positivity, fun f hf X z hz hz1 p q hq => ?_⟩
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hzc : z ∈ closedBall (0 : Euc d) 1 := by simpa using hz1
  have hnest : ∀ K : ℝ, 0 ≤ K → (∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ,
      ‖iteratedFDeriv ℝ q (r26t8a_R3_G nu chi B) z‖ ≤ K * ‖B‖) →
      ‖r26t8a_nest p q (fun Yw : Euc d × Euc d =>
          s82n_leadingInverse nu (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2 +
            r26t8a_p22_S0 nu chi (fderiv ℝ (fderiv ℝ f) Yw.1) Yw.2) X z‖ ≤
        K * ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ := fun K hK0 hK =>
    r26t8a_R3_nest_Phi_core hd nu hchi hf X z hz p q K hK0 hK
  have hDp : 0 ≤ ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ := norm_nonneg _
  have hr1 : 0 ≤ ‖z‖ ^ (2 - s82n_critS d) := Real.rpow_nonneg hzn.le _
  have hr2 : 0 ≤ ‖z‖ ^ (1 - s82n_critS d) := Real.rpow_nonneg hzn.le _
  have hr3 : 0 ≤ ‖z‖ ^ (-s82n_critS d) := Real.rpow_nonneg hzn.le _
  have hlg : 0 ≤ (if d = 4 then |Real.log ‖z‖| else (0 : ℝ)) := by split_ifs <;> positivity
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 := by omega
  rcases hq' with rfl | rfl | rfl
  · have hK : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, ‖iteratedFDeriv ℝ 0 (r26t8a_R3_G nu chi B) z‖ ≤
        ((CL + C0) * (1 + ‖z‖ ^ (2 - s82n_critS d) + if d = 4 then |Real.log ‖z‖| else 0)) * ‖B‖ := by
      intro B
      rw [r26t8a_R3_G_iter hd nu hchi hz]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖iteratedFDeriv ℝ 0 (s82n_leadingInverse nu B) z‖ ≤
          CL * ‖B‖ * (‖z‖ ^ (2 - s82n_critS d) + if d = 4 then |Real.log ‖z‖| else 0) := by
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact (hCL B z hz).1
      have h2 := hC0 B z hzc
      have hB0 : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
      nlinarith [mul_nonneg hCL0 hB0, mul_nonneg hC00 hB0, mul_nonneg (mul_nonneg hCL0 hB0) hr1,
        mul_nonneg (mul_nonneg hCL0 hB0) hlg, mul_nonneg (mul_nonneg hC00 hB0) hr1, mul_nonneg (mul_nonneg hC00 hB0) hlg]
    refine (hnest _ (mul_nonneg (add_nonneg hCL0 hC00) (add_nonneg (add_nonneg zero_le_one hr1) hlg)) hK).trans ?_
    have e : ‖z‖ ^ (-((s82n_critS d - 2) + ((0 : ℕ) : ℝ))) = ‖z‖ ^ (2 - s82n_critS d) := by
      congr 1; push_cast; ring
    rw [e, if_pos rfl]
    have hE : 0 ≤ 1 + ‖z‖ ^ (2 - s82n_critS d) + (if d = 4 then |Real.log ‖z‖| else 0) :=
      add_nonneg (add_nonneg zero_le_one hr1) hlg
    have hle : CL + C0 ≤ CL + CH + C0 + C1 + C2 := by linarith
    calc (CL + C0) * (1 + ‖z‖ ^ (2 - s82n_critS d) + (if d = 4 then |Real.log ‖z‖| else 0)) *
          ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖
        = (CL + C0) * (‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ *
          (1 + ‖z‖ ^ (2 - s82n_critS d) + (if d = 4 then |Real.log ‖z‖| else 0))) := by ring
      _ ≤ (CL + CH + C0 + C1 + C2) * (‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ *
          (1 + ‖z‖ ^ (2 - s82n_critS d) + (if d = 4 then |Real.log ‖z‖| else 0))) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hDp hE)
      _ = _ := by ring
  · have hK : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, ‖iteratedFDeriv ℝ 1 (r26t8a_R3_G nu chi B) z‖ ≤
        ((CL + C1) * (1 + ‖z‖ ^ (1 - s82n_critS d))) * ‖B‖ := by
      intro B
      rw [r26t8a_R3_G_iter hd nu hchi hz]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖iteratedFDeriv ℝ 1 (s82n_leadingInverse nu B) z‖ ≤ CL * ‖B‖ * ‖z‖ ^ (1 - s82n_critS d) := by
        rw [r26t8a_R3_iter_norm_fderiv]; exact (hCL B z hz).2
      have h2 := hC1 B z hzc
      have hB0 : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
      nlinarith [mul_nonneg hCL0 hB0, mul_nonneg hC10 hB0, mul_nonneg (mul_nonneg hCL0 hB0) hr2,
        mul_nonneg (mul_nonneg hC10 hB0) hr2]
    refine (hnest _ (mul_nonneg (add_nonneg hCL0 hC10) (add_nonneg zero_le_one hr2)) hK).trans ?_
    have e : ‖z‖ ^ (-((s82n_critS d - 2) + ((1 : ℕ) : ℝ))) = ‖z‖ ^ (1 - s82n_critS d) := by
      congr 1; push_cast; ring
    rw [e, if_neg one_ne_zero, add_zero]
    have hE : 0 ≤ 1 + ‖z‖ ^ (1 - s82n_critS d) := add_nonneg zero_le_one hr2
    have hle : CL + C1 ≤ CL + CH + C0 + C1 + C2 := by linarith
    calc (CL + C1) * (1 + ‖z‖ ^ (1 - s82n_critS d)) * ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖
        = (CL + C1) * (‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ * (1 + ‖z‖ ^ (1 - s82n_critS d))) := by ring
      _ ≤ (CL + CH + C0 + C1 + C2) * (‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ * (1 + ‖z‖ ^ (1 - s82n_critS d))) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hDp hE)
      _ = _ := by ring
  · have hK : ∀ B : Euc d →L[ℝ] Euc d →L[ℝ] ℝ, ‖iteratedFDeriv ℝ 2 (r26t8a_R3_G nu chi B) z‖ ≤
        ((CH + C2) * (1 + ‖z‖ ^ (-s82n_critS d))) * ‖B‖ := by
      intro B
      rw [r26t8a_R3_G_iter hd nu hchi hz]
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖iteratedFDeriv ℝ 2 (s82n_leadingInverse nu B) z‖ ≤ CH * ‖B‖ * ‖z‖ ^ (-s82n_critS d) := by
        rw [r26t8a_R3_iter_norm_fderiv2]; exact hCH B z hz
      have h2 := hC2 B z hzc
      have hB0 : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
      nlinarith [mul_nonneg hCH0 hB0, mul_nonneg hC20 hB0, mul_nonneg (mul_nonneg hCH0 hB0) hr3,
        mul_nonneg (mul_nonneg hC20 hB0) hr3]
    refine (hnest _ (mul_nonneg (add_nonneg hCH0 hC20) (add_nonneg zero_le_one hr3)) hK).trans ?_
    have e : ‖z‖ ^ (-((s82n_critS d - 2) + ((2 : ℕ) : ℝ))) = ‖z‖ ^ (-s82n_critS d) := by
      congr 1; push_cast; ring
    rw [e, if_neg two_ne_zero, add_zero]
    have hE : 0 ≤ 1 + ‖z‖ ^ (-s82n_critS d) := add_nonneg zero_le_one hr3
    have hle : CH + C2 ≤ CL + CH + C0 + C1 + C2 := by linarith
    calc (CH + C2) * (1 + ‖z‖ ^ (-s82n_critS d)) * ‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖
        = (CH + C2) * (‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ * (1 + ‖z‖ ^ (-s82n_critS d))) := by ring
      _ ≤ (CL + CH + C0 + C1 + C2) * (‖iteratedFDeriv ℝ p (fderiv ℝ (fderiv ℝ f)) X‖ * (1 + ‖z‖ ^ (-s82n_critS d))) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg hDp hE)
      _ = _ := by ring

end HRS.MS.R26T8A
