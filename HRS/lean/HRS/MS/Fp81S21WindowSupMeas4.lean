import HRS.MS.Fp81S21WindowSupMeas3

/-! Physical drift supremum and its source certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- The drift bound is a genuine sixth moment, with source-time integrability
simultaneously from zero to any terminal time. -/
theorem fp81s21_window_drift_sup_moment6 (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ CD : ℝ, 0 ≤ CD ∧ ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N →
      ∀ A : Particle R N, ∀ b : ℝ, 0 ≤ b → ∀ α : MultiIndex p.d,
      fp81s21_Moment6 A.P (fun ω => ⨆ t : Icc b (b + H),
        |∫ v in b..(t : ℝ), fp81s21_window_mode_source_field p R A α v t ω|)
        ((CD * (H + H ^ 2) * s104_b p.d α) ^ 6) ∧
      (∀ᵐ ω ∂A.P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable (fun v => fp81s21_window_mode_source_field p R A α v t ω)
          volume a t) := by
  obtain ⟨δa, ha, hah, hsup⟩ := fp81s21_window_drift_sup_sixth p
  obtain ⟨δb, hb, hbh, hprim⟩ := fp81s21_window_mode_drift_constructed p
  refine ⟨min δa δb, lt_min ha hb, (min_le_left _ _).trans hah, ?_⟩
  intro δ hδ hδle R
  obtain ⟨CD, hCD, hbound⟩ := hsup δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨C, L, hC, hL, hdata⟩ := hprim δ hδ (hδle.trans (min_le_right _ _)) R
  refine ⟨CD, hCD, ?_⟩
  intro H hH N hN A b hb0 α
  have hT : 0 < b + H := by linarith
  obtain ⟨_, _, Q, K, hQ, hK, hQe, hKe, hQi, hKi, hsource, hcont, hmeas⟩ :=
    hdata N hN A (b + H) hT α b hb0 (by linarith)
  let X : ℝ → A.Ω → ℝ := fun t ω => ∫ v in b..t,
    fp81s21_window_mode_source_field p R A α v t ω
  have hc : ∀ᵐ ω ∂A.P, ContinuousOn (fun t => X t ω) (Icc b (b + H)) := by
    filter_upwards [hcont] with ω hω
    exact hω.2
  have hm : ∀ t ∈ Icc b (b + H), AEMeasurable (X t) A.P := hmeas
  have hM : 0 ≤ CD * (H + H ^ 2) * s104_b p.d α := by
    exact mul_nonneg (mul_nonneg hCD (by positivity)) (s104_b_nonneg α)
  have hbound' : (∫⁻ ω, (⨆ t : Icc b (b + H), ‖X t ω‖ₑ) ^ (6 : ℝ) ∂A.P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal (CD * (H + H ^ 2) * s104_b p.d α) := by
    simpa [X, fp81s21_window_mode_source_field, Real.enorm_eq_ofReal_abs] using
      hbound H hH N hN A b hb0 α
  have hmom := fp81s21_window_sup_moment6 A.P X b (b + H)
    (CD * (H + H ^ 2) * s104_b p.d α) (by linarith) hM hm hc hbound'
  refine ⟨?_, hsource⟩
  simpa [X, Real.norm_eq_abs] using hmom

#print axioms fp81s21_window_drift_sup_moment6
end HRS.Fp81.S21
end
