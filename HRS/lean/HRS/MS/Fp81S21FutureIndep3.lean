import HRS.MS.Fp81S21FutureIndep2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The past part of a terminal-time feature is orthogonal to every future
feature, even when the past part's terminal time lies after the cutoff. -/
theorem fp81s21_movingNoise_cutoff_parts_orthogonal
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r s t : ℝ} (hr : r ∈ Icc (0 : ℝ) H)
    (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ)
    (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ) :
    inner ℝ (movingNoiseFeature R 0 s φ - movingNoiseFeature R r s φ)
      (movingNoiseFeature R r t ψ) = 0 := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  have hpast := fp81s21_movingNoise_past_feature_ae p R hδ hδhalf hH hr hs hφ
  have hmem := (movingNoiseFeature_spec p R hδ hδhalf hH).1 r hr t ht ψ hψ
  have hfuture : (movingNoiseFeature R r t ψ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R r t ψ := by
    rw [movingNoiseFeature, dif_pos hmem]
    exact hmem.coeFn_toLp
  have hne : ∀ᵐ q ∂μ, q.1 ≠ r := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst (measurableSet_singleton r).compl)).2
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) r] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hpast, hfuture, hne] with q hp hf hq
  rw [hp, hf]
  by_cases hqr : q.1 ≤ r
  · have hnot : q.1 ∉ Icc r t := by
      intro hm
      exact hq (le_antisymm hqr hm.1)
    simp [hqr, movingNoiseKernel, hnot]
  · simp [hqr]

#print axioms fp81s21_movingNoise_cutoff_parts_orthogonal

end HRS.Fp81.S21
end
