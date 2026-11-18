import HRS.MS.Fp81S21DriftBV2

/-! The scalar control for clipped interval increments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

variable {Q H b h K : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b) (hh : 0 ≤ h)
  (hhH : h ≤ H) (hbQ : b + h ≤ Q) (hK : 0 ≤ K)

include hb hh hbQ in
private theorem clip_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) H) :
    b + min s h ∈ Icc (0 : ℝ) Q := by
  constructor
  · have : 0 ≤ min s h := le_min hs.1 hh
    linarith
  · have hm : min s h ≤ h := min_le_right _ _
    linarith

private theorem clip_mono {s t : ℝ} (hst : s ≤ t) :
    b + min s h ≤ b + min t h := by
  simpa [add_comm] using add_le_add_left (min_le_min_right h hst) b

private theorem norm_int (q : r26t6_TimeCoeff Q) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ Q) :
    IntervalIntegrable (fun z => ‖q z‖) volume v w := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hvw).2
  have hi : IntegrableOn (fun z => ‖q z‖) (Icc (0 : ℝ) Q) volume :=
    (Lp.memLp q |>.integrable le_rfl).norm
  exact hi.mono_set (Icc_subset_Icc hv hw)

include hH hb hh hhH hbQ hK in
/-- The clipped control has monotone increments and total mass at most `K * ‖q‖`. -/
theorem fp81s21_clippedControl_properties (q : r26t6_TimeCoeff Q) :
    MonotoneOn (fp81s21_clippedControl (b := b) (h := h) (K := K) q) (Icc 0 H) ∧
    (∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, s ≤ t →
      K * (∫ z in Ioc (b + min s h) (b + min t h), ‖q z‖) =
        fp81s21_clippedControl (b := b) (h := h) (K := K) q t -
          fp81s21_clippedControl (b := b) (h := h) (K := K) q s) ∧
    fp81s21_clippedControl (b := b) (h := h) (K := K) q H -
      fp81s21_clippedControl (b := b) (h := h) (K := K) q 0 ≤ K * ‖q‖ := by
  have hleft (s : ℝ) (hs : s ∈ Icc (0 : ℝ) H) : b ≤ b + min s h := by
    have : 0 ≤ min s h := le_min hs.1 hh
    linarith
  have hdiff (s : ℝ) (hs : s ∈ Icc (0 : ℝ) H) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) H) (hst : s ≤ t) :
      K * (∫ z in Ioc (b + min s h) (b + min t h), ‖q z‖) =
        fp81s21_clippedControl (b := b) (h := h) (K := K) q t -
          fp81s21_clippedControl (b := b) (h := h) (K := K) q s := by
    have hsQ := (clip_mem hb hh hbQ hs).2
    have htQ := (clip_mem hb hh hbQ ht).2
    have hst' : b + min s h ≤ b + min t h := clip_mono hst
    have h1 := norm_int q hb (hleft s hs) hsQ
    have h2 := norm_int q ((clip_mem hb hh hbQ hs).1) hst' htQ
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    rw [intervalIntegral.integral_of_le hst'] at hadd
    unfold fp81s21_clippedControl
    nlinarith [hadd]
  refine ⟨?_, hdiff, ?_⟩
  · intro s hs t ht hst
    have hi := hdiff s hs t ht hst
    have hp : 0 ≤ K * (∫ z in Ioc (b + min s h) (b + min t h), ‖q z‖) :=
      mul_nonneg hK (integral_nonneg fun z => norm_nonneg _)
    linarith
  · have heq : min H h = h := min_eq_right hhH
    have hz : min (0 : ℝ) h = 0 := min_eq_left hh
    simp only [fp81s21_clippedControl, heq, hz, add_zero, intervalIntegral.integral_same,
      mul_zero, sub_zero, intervalIntegral.integral_of_le (by linarith : b ≤ b + h)]
    apply mul_le_mul_of_nonneg_left _ hK
    have hi : IntegrableOn (fun z => ‖q z‖) (Icc (0 : ℝ) Q) volume :=
      (Lp.memLp q |>.integrable le_rfl).norm
    have hsub : Ioc b (b + h) ⊆ Icc (0 : ℝ) Q := fun z hz => ⟨hb.trans hz.1.le, hz.2.trans hbQ⟩
    rw [MeasureTheory.L1.norm_eq_integral_norm]
    exact setIntegral_mono_set hi (Filter.Eventually.of_forall fun z => norm_nonneg _)
      (Filter.Eventually.of_forall hsub)

#print axioms fp81s21_clippedControl_properties
end HRS.Fp81.S21
end
