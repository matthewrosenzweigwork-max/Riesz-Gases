import HRS.Equilibrium.Parametrix.PXFIDAuxE

/-!
# Packet PX-FID, file F: the vanishing flux (integration by parts) for a singular slice
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

theorem grad_theta_zero {ε : ℝ} (hε : 0 < ε) (ã : Euc d) (x : Torus d)
    (h : ε / 2 < Torus.eucDist x (Torus.mk ã)) : Torus.grad (theta ε ã) x = 0 := by
  unfold Torus.grad gradient
  rw [fderiv_theta_eq_zero hε ã (Torus.rep x) (by rw [Torus.mk_rep]; exact h)]
  simp

theorem exists_norm_grad_theta_le (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (ã : Euc d)
    (x : Torus d), ‖Torus.grad (theta ε ã) x‖ ≤ C / Torus.eucDist x (Torus.mk ã) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_fderiv_theta_le d
  refine ⟨C, hC0, fun ε hε ã x => ?_⟩
  have h := hC ε hε ã (Torus.rep x)
  rw [Torus.mk_rep] at h
  have h2 : ‖Torus.grad (theta ε ã) x‖ = ‖fderiv ℝ (Torus.lift (theta ε ã)) (Torus.rep x)‖ := by
    unfold Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  rw [h2]; exact h

theorem measurable_theta (ε : ℝ) (ã : Euc d) : Measurable (theta ε ã) :=
  (Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift (theta ε ã)) from theta_isSmooth ε ã).continuous).measurable

theorem measurable_of_isSmooth {ϕ : Torus d → ℝ} (hϕ : Torus.IsSmooth ϕ) : Measurable ϕ :=
  (Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift ϕ) from hϕ).continuous).measurable

/-- Domination of the cut-off gradient term. -/
theorem F3_bound (hs1 : 1 ≤ s) {K Cθ Mϕ : ℝ} (hK : 0 ≤ K) (hCθ0 : 0 ≤ Cθ) (hMϕ0 : 0 ≤ Mϕ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {ã : Euc d} {u ϕ : Torus d → ℝ}
    (hCθ : ∀ (ε : ℝ), 0 < ε → ∀ (ã : Euc d) (x : Torus d),
      ‖Torus.grad (theta ε ã) x‖ ≤ Cθ / Torus.eucDist x (Torus.mk ã))
    (hu : SingSlice s K ã u) (hϕ : ∀ x, |ϕ x| ≤ Mϕ) (x : Torus d) (hx : x ≠ Torus.mk ã) :
    ‖ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x)‖ ≤
      Mϕ * (2 * Cθ * K) * wEnv s x (Torus.mk ã) := by
  have hw1 := PairCorrAux.one_le_wEnv s x (Torus.mk ã)
  have hpos : 0 ≤ Mϕ * (2 * Cθ * K) * wEnv s x (Torus.mk ã) := by positivity
  set D := Torus.eucDist x (Torus.mk ã) with hD
  by_cases hfar : ε / 2 < D
  · rw [grad_theta_zero hε ã x hfar]
    simpa using hpos
  · push Not at hfar
    have hD0 : 0 < D := by
      rcases (Real.sqrt_nonneg _ : 0 ≤ D).lt_or_eq with h | h
      · exact h
      · exact absurd ((PairCorrAux.eucDist_eq_zero' _ _).1 h.symm) hx
    have hD1 : D ≤ 1 := by linarith
    have hr : rTrunc x (Torus.mk ã) = D := by unfold rTrunc; rw [min_eq_right hD1]
    have h1 := hCθ ε hε ã x
    have h2 := hu.norm_grad_le' x hx
    rw [hr] at h2
    have hw : wEnv s x (Torus.mk ã) = 1 + D ^ (-s) := by unfold wEnv; rw [hr]
    have hDs : D⁻¹ ≤ D ^ (-s) := by
      have e : D ^ (-s) = D⁻¹ * D ^ (1 - s) := by
        rw [show -s = (-1) + (1 - s) by ring, Real.rpow_add hD0, Real.rpow_neg_one]
      have h3 : 1 ≤ D ^ (1 - s) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hD0 hD1 (by linarith)
      rw [e]
      nlinarith [inv_pos.2 hD0]
    have e2 : D⁻¹ * D ^ (1 - s) = D ^ (-s) := by
      rw [show -s = (-1) + (1 - s) by ring, Real.rpow_add hD0, Real.rpow_neg_one]
    have hDsn : 0 ≤ D ^ (-s) := Real.rpow_nonneg hD0.le _
    calc ‖ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x)‖
        = |ϕ x| * |inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x)| := by
          rw [Real.norm_eq_abs, abs_mul]
      _ ≤ Mϕ * (‖Torus.grad (theta ε ã) x‖ * ‖Torus.grad u x‖) :=
          mul_le_mul (hϕ x) (abs_real_inner_le_norm _ _) (abs_nonneg _) hMϕ0
      _ ≤ Mϕ * ((Cθ / D) * (K * (1 + D ^ (1 - s)))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hMϕ0
      _ = Mϕ * (Cθ * K * (D⁻¹ + D ^ (-s))) := by
          rw [← e2]; field_simp
      _ ≤ Mϕ * (2 * Cθ * K * (1 + D ^ (-s))) := by
          refine mul_le_mul_of_nonneg_left ?_ hMϕ0
          have : 0 ≤ Cθ * K := mul_nonneg hCθ0 hK
          nlinarith
      _ = Mϕ * (2 * Cθ * K) * wEnv s x (Torus.mk ã) := by rw [hw]; ring

end HRS.Parx.PXFID

end
