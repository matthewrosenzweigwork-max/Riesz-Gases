import HRS.MS.Fp81S21DriftBV

/-! Clipped cumulative interval controls. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

variable {Q H b h K : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b) (hh : 0 ≤ h)
  (hhH : h ≤ H) (hbQ : b + h ≤ Q) (hK : 0 ≤ K)

include hb hh hbQ in
private theorem fp81s21_clip_mem {s : ℝ} (hs : s ∈ Icc (0 : ℝ) H) :
    b + min s h ∈ Icc (0 : ℝ) Q := by
  constructor
  · have : 0 ≤ min s h := le_min hs.1 hh
    linarith
  · have hm : min s h ≤ h := min_le_right _ _
    linarith

private theorem fp81s21_clip_mono {s t : ℝ} (hst : s ≤ t) :
    b + min s h ≤ b + min t h := by
  simpa [add_comm] using add_le_add_left (min_le_min_right h hst) b

private theorem fp81s21_norm_int (q : r26t6_TimeCoeff Q) {v w : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w ≤ Q) :
    IntervalIntegrable (fun z => ‖q z‖) volume v w := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hvw).2
  have hi : IntegrableOn (fun z => ‖q z‖) (Icc (0 : ℝ) Q) volume :=
    (Lp.memLp q |>.integrable le_rfl).norm
  exact hi.mono_set (Icc_subset_Icc hv hw)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (D : ℝ → ℝ → r26t6_TimeCoeff Q →L[ℝ] E)
  (dz : ∀ v, D v v = 0)
  (da : ∀ v w z, 0 ≤ v → v ≤ w → w ≤ z → z ≤ Q → D v z = D v w + D w z)
  (dc : ∀ q, ContinuousOn (fun v => D 0 v q) (Icc 0 Q))
  (dn : ∀ v w, 0 ≤ v → v ≤ w → w ≤ Q → ∀ q,
    ‖D v w q‖ ≤ K * ∫ z in Ioc v w, ‖q z‖)

/-- Interval increments with the source-time coordinate clipped at `h`. -/
def fp81s21_clippedDelta (s t : ℝ) : r26t6_TimeCoeff Q →L[ℝ] E :=
  D (b + min s h) (b + min t h)

/-- A scalar control for clipped increments, using the source L¹ norm. -/
def fp81s21_clippedControl (q : r26t6_TimeCoeff Q) (t : ℝ) : ℝ :=
  K * ∫ z in b..(b + min t h), ‖q z‖

#print axioms fp81s21_clippedDelta
#print axioms fp81s21_clippedControl
end HRS.Fp81.S21
end
