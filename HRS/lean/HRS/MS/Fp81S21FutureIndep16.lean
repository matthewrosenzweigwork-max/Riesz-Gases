import HRS.MS.Fp81S21FutureIndep9

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- A future observation feature belongs to the complete supported future
noise space; the shared endpoint is null for time-space Lebesgue measure. -/
theorem fp81s21_future_feature_supported
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ : Euc p.d → ℝ} (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    movingNoiseFeature R r t φ ∈ fp81s21_FutureNoiseFeatures p.d r := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  have hmem := (movingNoiseFeature_spec p R hδ hδhalf hH).1 r hr t ht φ hφ
  have hfeature : (movingNoiseFeature R r t φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R r t φ := by
    rw [movingNoiseFeature, dif_pos hmem]
    exact hmem.coeFn_toLp
  have hne : ∀ᵐ q ∂μ, q.1 ≠ r := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst (measurableSet_singleton r).compl)).2
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) r] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  change ∀ᵐ q ∂μ, q.1 ≤ r → movingNoiseFeature R r t φ q = 0
  filter_upwards [hfeature, hne] with q hq hqr hle
  rw [hq]
  have hnot : q.1 ∉ Icc r t := by
    intro hm
    exact hqr (le_antisymm hle hm.1)
  simp [movingNoiseKernel, hnot]

#print axioms fp81s21_future_feature_supported

end HRS.Fp81.S21
end
