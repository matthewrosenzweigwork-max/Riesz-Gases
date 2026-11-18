import HRS.MS.Fp81S21FutureIndep

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The difference between the full and future features is the same
terminal-time kernel restricted to the absolute past. This remains valid for
times on either side of the cutoff. -/
theorem fp81s21_movingNoise_past_feature_ae
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ} (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    ((movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ :
        MovingNoiseHilbert p.d) : ℝ × Euc p.d → Euc p.d) =ᵐ[
          (volume : Measure ℝ).prod (volume : Measure (Euc p.d))]
      fun q => if q.1 ≤ r then movingNoiseKernel R 0 t φ q else 0 := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  have hmem1 := (movingNoiseFeature_spec p R hδ hδhalf hH).1 0
    ⟨le_rfl, hH.le⟩ t ht φ hφ
  have hmem2 := (movingNoiseFeature_spec p R hδ hδhalf hH).1 r hr t ht φ hφ
  have h1 : (movingNoiseFeature R 0 t φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R 0 t φ := by
    rw [movingNoiseFeature, dif_pos hmem1]
    exact hmem1.coeFn_toLp
  have h2 : (movingNoiseFeature R r t φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R r t φ := by
    rw [movingNoiseFeature, dif_pos hmem2]
    exact hmem2.coeFn_toLp
  have hne : ∀ᵐ q ∂μ, q.1 ≠ r := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst (measurableSet_singleton r).compl)).2
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) r] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  filter_upwards [Lp.coeFn_sub (movingNoiseFeature R 0 t φ)
    (movingNoiseFeature R r t φ), h1, h2, hne] with q hsub hq1 hq2 hqr
  rw [hsub, Pi.sub_apply, hq1, hq2]
  by_cases hqt : q.1 ∈ Icc (0 : ℝ) t
  · by_cases hqrle : q.1 ≤ r
    · have hnot : q.1 ∉ Icc r t := by
        intro hm
        exact hqr (le_antisymm hqrle hm.1)
      simp [hqrle, movingNoiseKernel, hnot]
    · have hm : q.1 ∈ Icc r t := ⟨le_of_lt (lt_of_not_ge hqrle), hqt.2⟩
      simp [hqrle, movingNoiseKernel, hqt, hm]
  · have hnot : q.1 ∉ Icc r t := by
      intro hm
      exact hqt ⟨hr.1.trans hm.1, hm.2⟩
    simp [movingNoiseKernel, hqt, hnot]

#print axioms fp81s21_movingNoise_past_feature_ae

end HRS.Fp81.S21
end
