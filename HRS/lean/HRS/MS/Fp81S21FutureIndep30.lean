import HRS.MS.Fp81S21FutureIndep29
import HRS.MS.Fp81S21FutureIndep10

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- The propagated test's retained initial-plus-noise feature is exactly the
initial-and-past portion of the terminal oscillator test's feature. -/
theorem fp81s21_propagated_combined_feature
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hrt : r ≤ t) {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    fp81s21_combinedFeature p R hK r (propagatorW (r26t3_coeff R) r t φ) =
      WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
        movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ) := by
  have hc := fp81s21_moving_propagator_comp p R (v := 0) le_rfl hr.1 hrt hφ
  have hi : fp81s21_initialGaussianFeature p R hK r
      (propagatorW (r26t3_coeff R) r t φ) =
      fp81s21_initialGaussianFeature p R hK t φ := by
    simp only [fp81s21_initialGaussianFeature, initialGaussianFeature, hc]
  have hn := (fp81s21_propagated_noise_feature p R hδ hδhalf hH hr ht hrt hφ).2
  simp only [fp81s21_combinedFeature, hi, hn]

/-- The Gaussian evaluation at the terminal test decomposes into the
propagated test's retained-source evaluation and the independent future source. -/
theorem fp81s21_propagated_source_decomposition
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h)) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hrt : r ≤ t) {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    ∀ᵐ ω ∂P, W (J (fp81s21_combinedFeature p R hK t φ)) ω =
      W (J (fp81s21_combinedFeature p R hK r (propagatorW (r26t3_coeff R) r t φ))) ω +
      W (J (fp81s21_futureNoiseSourceFeature p R r t φ)) ω := by
  have h := fp81s21_combined_source_decomposition p R hK P J W hWm hW2 hcomb r t φ
  rw [fp81s21_propagated_combined_feature p R hδ hδhalf hH hK hr ht hrt hφ]
  exact h

#print axioms fp81s21_propagated_combined_feature
#print axioms fp81s21_propagated_source_decomposition
end HRS.Fp81.S21
end
