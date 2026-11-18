import HRS.MS.Fp81S21DriftBV3

/-! Lift clipped interval operators to variation-norm paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

variable {Q H b h K : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (hH : 0 ≤ H) (hb : 0 ≤ b) (hh : 0 ≤ h) (hhH : h ≤ H)
  (hbQ : b + h ≤ Q) (hK : 0 ≤ K)
  (D : ℝ → ℝ → r26t6_TimeCoeff Q →L[ℝ] E)
  (dz : ∀ v, D v v = 0)
  (da : ∀ v w z, 0 ≤ v → v ≤ w → w ≤ z → z ≤ Q → D v z = D v w + D w z)
  (dc : ∀ q, ContinuousOn (fun v => D 0 v q) (Icc 0 Q))
  (dn : ∀ v w, 0 ≤ v → v ≤ w → w ≤ Q → ∀ q,
    ‖D v w q‖ ≤ K * ∫ z in Ioc v w, ‖q z‖)

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

/-- Abstract clipped interval operators with an L¹ increment bound define BV data. -/
def fp81s21_clippedIntervalBVData :
    fp81s21_IntervalBVData (X := r26t6_TimeCoeff Q) (E := E) (H := H) K where
  delta := fp81s21_clippedDelta (b := b) (h := h) D
  zero := by simpa [fp81s21_clippedDelta, min_eq_left hh] using dz b
  add := by
    intro s hs t ht hst
    have ht' := clip_mem hb hh hbQ ht
    have hs0 : b ≤ b + min s h := by
      have : 0 ≤ min s h := le_min hs.1 hh
      linarith
    simpa [fp81s21_clippedDelta, min_eq_left hh] using
      da b (b + min s h) (b + min t h) hb hs0 (clip_mono hst) ht'.2
  cont := by
    intro q
    have ht : Continuous (fun s : ℝ => b + min s h) :=
      continuous_const.add (continuous_id.min continuous_const)
    have hc : ContinuousOn (fun s : ℝ => D 0 (b + min s h) q) (Icc 0 H) :=
      (dc q).comp ht.continuousOn (fun s hs => clip_mem hb hh hbQ hs)
    have hc' : ContinuousOn (fun s : ℝ => D 0 (b + min s h) q - D 0 b q) (Icc 0 H) :=
      hc.sub continuousOn_const
    apply hc'.congr
    intro s hs
    have hs0 : b ≤ b + min s h := by
      have : 0 ≤ min s h := le_min hs.1 hh
      linarith
    have hsQ := (clip_mem hb hh hbQ hs).2
    have hda := congrArg (fun F : r26t6_TimeCoeff Q →L[ℝ] E => F q)
      (da 0 b (b + min s h) le_rfl hb hs0 hsQ)
    simp only [ContinuousLinearMap.add_apply] at hda
    simp only [fp81s21_clippedDelta, min_eq_left hh, add_zero]
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using hda.symm
  control := fp81s21_clippedControl (b := b) (h := h) (K := K)
  control_mono := fun q => (fp81s21_clippedControl_properties hH hb hh hhH hbQ hK q).1
  inc_le := by
    intro q s hs t ht hst
    have hs' := clip_mem hb hh hbQ hs
    have ht' := clip_mem hb hh hbQ ht
    have h := dn (b + min s h) (b + min t h) hs'.1 (clip_mono hst) ht'.2 q
    exact h.trans_eq ((fp81s21_clippedControl_properties hH hb hh hhH hbQ hK q).2.1 s hs t ht hst)
  total_le := fun q => (fp81s21_clippedControl_properties hH hb hh hhH hbQ hK q).2.2

#print axioms fp81s21_clippedIntervalBVData
end HRS.Fp81.S21
end
