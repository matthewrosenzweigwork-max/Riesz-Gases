import HRS.MS.Fp81S21WindowSupMeas5

/-! Uniform physical initial and drift window moments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2WinErr

/-- Initial and drift window suprema have uniform sixth moments; the drift
source integrability certificate holds simultaneously from time zero. -/
theorem fp81s21_window_initial_drift_moment6 (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ CI CD : ℝ, 0 ≤ CI ∧ 0 ≤ CD ∧
      ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ b : ℝ, 0 ≤ b → ∀ α : MultiIndex p.d,
      fp81s21_Moment6 A.P (fun ω => ⨆ t : Icc b (b + H),
        |s102_zf A.P A.X ω b (propagatorW (r26t3_coeff R) b t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α))|)
        ((CI * (1 + H) * s104_b p.d α) ^ 6) ∧
      fp81s21_Moment6 A.P (fun ω => ⨆ t : Icc b (b + H),
        |∫ v in b..(t : ℝ), fp81s21_window_mode_source_field p R A α v t ω|)
        ((CD * (H + H ^ 2) * s104_b p.d α) ^ 6) ∧
      (∀ᵐ ω ∂A.P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable (fun v => fp81s21_window_mode_source_field p R A α v t ω)
          volume a t) := by
  obtain ⟨δa, ha, hah, hinitial⟩ := fp81s21_window_initial_sup_sixth p
  obtain ⟨δb, hb, hbh, hdrift⟩ := fp81s21_window_drift_sup_moment6 p
  obtain ⟨δc, Co, co, hc, hch, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨min δa (min δb δc), lt_min ha (lt_min hb hc),
    (min_le_left _ _).trans hah, ?_⟩
  intro δ hδ hδle R
  obtain ⟨CI, hCI, hbound⟩ := hinitial δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨CD, hCD, hD⟩ := hdrift δ hδ
    (hδle.trans ((min_le_right _ _).trans (min_le_left _ _))) R
  obtain ⟨hClaims, _, hTerm, _⟩ := hcommon δ hδ
    (hδle.trans ((min_le_right _ _).trans (min_le_right _ _))) R.ρβ R.thermal
  refine ⟨CI, CD, hCI, hCD, ?_⟩
  intro H hH N hN A b hb0 α
  have hT : 0 < b + H := by linarith
  have hbT : b ∈ Icc (0 : ℝ) (b + H) := ⟨hb0, by linarith⟩
  obtain ⟨_, hData⟩ := fp81s21_moving_s101data_of_common p R hT hClaims hTerm
  have hX : Measurable (A.X b.toNNReal) := (A.strong (b + H)).adapted b.toNNReal
  have hNpos : 0 < N := by omega
  let X : ℝ → A.Ω → ℝ := fun t ω => s102_zf A.P A.X ω b
    (propagatorW (r26t3_coeff R) b t (oscTestFun (wholeSpaceIndex p.d : ℝ) α))
  obtain ⟨hcX, hmX⟩ := fp81s21_initial_coordinate_regular A.P A.X hData hbT hX hNpos α
  have hm : ∀ t ∈ Icc b (b + H), AEMeasurable (X t) A.P :=
    fun t ht => (hmX t ht).aemeasurable
  have hc : ∀ᵐ ω ∂A.P, ContinuousOn (fun t => X t ω) (Icc b (b + H)) :=
    Filter.Eventually.of_forall hcX
  have hM : 0 ≤ CI * (1 + H) * s104_b p.d α :=
    mul_nonneg (mul_nonneg hCI (by linarith)) (s104_b_nonneg α)
  have hbound' : (∫⁻ ω, (⨆ t : Icc b (b + H), ‖X t ω‖ₑ) ^ (6 : ℝ) ∂A.P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal (CI * (1 + H) * s104_b p.d α) := by
    simpa [X, Real.enorm_eq_ofReal_abs] using hbound H hH N hN A b hb0 α
  have hmom := fp81s21_window_sup_moment6 A.P X b (b + H)
    (CI * (1 + H) * s104_b p.d α) (by linarith) hM hm hc hbound'
  refine ⟨?_, hD H hH N hN A b hb0 α⟩
  simpa [X, Real.norm_eq_abs] using hmom

#print axioms fp81s21_window_initial_drift_moment6
end HRS.Fp81.S21
end
