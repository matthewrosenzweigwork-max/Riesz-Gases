import HRS.MS.Fp81S21MovingNoise

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- Noise features supported before and after an absolute cutoff are orthogonal.
The shared endpoint has zero time-space Lebesgue measure. -/
theorem fp81s21_movingNoise_past_future_orthogonal
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r s t : ℝ} (hr : r ∈ Icc (0 : ℝ) H)
    (hs : s ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hsr : s ≤ r) {φ ψ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ)
    (hψ : IsOscTest (wholeSpaceIndex p.d : ℝ) ψ) :
    inner ℝ (movingNoiseFeature R 0 s φ) (movingNoiseFeature R r t ψ) = 0 := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  have hmem1 := (movingNoiseFeature_spec p R hδ hδhalf hH).1 0
    ⟨le_rfl, hH.le⟩ s hs φ hφ
  have hmem2 := (movingNoiseFeature_spec p R hδ hδhalf hH).1 r hr t ht ψ hψ
  have h1 : (movingNoiseFeature R 0 s φ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R 0 s φ := by
    rw [movingNoiseFeature, dif_pos hmem1]
    exact hmem1.coeFn_toLp
  have h2 : (movingNoiseFeature R r t ψ : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R r t ψ := by
    rw [movingNoiseFeature, dif_pos hmem2]
    exact hmem2.coeFn_toLp
  have hne : ∀ᵐ q ∂μ, q.1 ≠ r := by
    apply (Measure.ae_prod_iff_ae_ae (measurable_fst (measurableSet_singleton r).compl)).2
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) r] with x hx
    exact Filter.Eventually.of_forall (fun _ => hx)
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [h1, h2, hne] with q hq1 hq2 hqr
  rw [hq1, hq2]
  by_cases hq : q.1 ∈ Icc (0 : ℝ) s
  · have hnot : q.1 ∉ Icc r t := by
      intro hm
      have : q.1 = r := le_antisymm (hq.2.trans hsr) hm.1
      exact hqr this
    simp [movingNoiseKernel, hnot]
  · simp [movingNoiseKernel, hq]

#print axioms fp81s21_movingNoise_past_future_orthogonal

end HRS.Fp81.S21
end
