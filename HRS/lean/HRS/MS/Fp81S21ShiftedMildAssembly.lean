import HRS.MS.Fp81S21DriftPrimitive9

/-! Exact shifted drift subtraction for the packet 10 mild identity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- The actual shifted drift appearing in the mild identity. -/
def fp81s21_shiftedModeDrift
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (α : MultiIndex p.d) (b t : ℝ) (ω : A.Ω) : ℝ :=
  ∫ v in b..t, fp81s21_window_mode_source_field p R A α v t ω

/-- Subtracting the initial source integral from the terminal one over the
adjacent intervals gives exactly the inverse-square-root drift contribution.
The integrability premises are the two instances supplied by the simultaneous
source certificate. -/
theorem fp81s21_shifted_mode_drift_subtraction
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (α : MultiIndex p.d) {b t : ℝ}
    (hb : 0 ≤ b) (hbt : b ≤ t) (ω : A.Ω)
    (h0b : IntervalIntegrable
      (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume 0 b)
    (hbtI : IntervalIntegrable
      (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume b t) :
    (∫ v in Icc (0 : ℝ) t,
      (-(Real.sqrt (N : ℝ))⁻¹ *
        fp81s21_window_mode_source_field p R A α v t ω)) -
    (∫ v in Icc (0 : ℝ) b,
      (-(Real.sqrt (N : ℝ))⁻¹ *
        fp81s21_window_mode_source_field p R A α v t ω)) =
      -(Real.sqrt (N : ℝ))⁻¹ * fp81s21_shiftedModeDrift p R A α b t ω := by
  let c : ℝ := -(Real.sqrt (N : ℝ))⁻¹
  let f : ℝ → ℝ := fun v => c * fp81s21_window_mode_source_field p R A α v t ω
  have h0b' : IntervalIntegrable f volume 0 b := by
    exact h0b.const_mul c
  have hbtI' : IntervalIntegrable f volume b t := by
    exact hbtI.const_mul c
  have hsum := intervalIntegral.integral_add_adjacent_intervals h0b' hbtI'
  have ht0 : 0 ≤ t := hb.trans hbt
  have hIt : (∫ v in Icc (0 : ℝ) t, f v) = ∫ v in (0 : ℝ)..t, f v := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht0]
  have hIb : (∫ v in Icc (0 : ℝ) b, f v) = ∫ v in (0 : ℝ)..b, f v := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb]
  calc
    (∫ v in Icc (0 : ℝ) t, f v) - (∫ v in Icc (0 : ℝ) b, f v) =
        (∫ v in (0 : ℝ)..t, f v) - (∫ v in (0 : ℝ)..b, f v) := by rw [hIt, hIb]
    _ = ∫ v in b..t, f v := by linarith [hsum]
    _ = -(Real.sqrt (N : ℝ))⁻¹ * fp81s21_shiftedModeDrift p R A α b t ω := by
      simp [f, c, fp81s21_shiftedModeDrift,
        intervalIntegral.integral_const_mul]

/-- On the one event supplied by the source certificate, the subtraction above
holds simultaneously for every terminal time in the shifted window. -/
theorem fp81s21_shifted_mode_drift_subtraction_ae
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (α : MultiIndex p.d) {b H : ℝ}
    (hb : 0 ≤ b) (hH : 0 < H)
    (hsource : ∀ᵐ ω ∂A.P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
      IntervalIntegrable
        (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) :
    ∀ᵐ ω ∂A.P, ∀ t ∈ Icc b (b + H),
      (∫ v in Icc (0 : ℝ) t,
        (-(Real.sqrt (N : ℝ))⁻¹ *
          fp81s21_window_mode_source_field p R A α v t ω)) -
      (∫ v in Icc (0 : ℝ) b,
        (-(Real.sqrt (N : ℝ))⁻¹ *
          fp81s21_window_mode_source_field p R A α v t ω)) =
        -(Real.sqrt (N : ℝ))⁻¹ * fp81s21_shiftedModeDrift p R A α b t ω := by
  filter_upwards [hsource] with ω hω
  intro t ht
  have h0t : IntervalIntegrable
      (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume 0 t :=
    hω 0 t (by norm_num) (le_trans hb ht.1) ht.2
  have h0b : IntervalIntegrable
      (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume 0 b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).2
    apply ((intervalIntegrable_iff_integrableOn_Icc_of_le
      (le_trans hb ht.1)).1 h0t).mono_set
    exact Icc_subset_Icc le_rfl ht.1
  have hbtI : IntervalIntegrable
      (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume b t :=
    hω b t hb ht.1 ht.2
  exact fp81s21_shifted_mode_drift_subtraction p R A α hb ht.1 ω h0b hbtI

#print axioms HRS.Fp81.S21.fp81s21_shifted_mode_drift_subtraction
#print axioms HRS.Fp81.S21.fp81s21_shifted_mode_drift_subtraction_ae

end HRS.Fp81.S21

end
