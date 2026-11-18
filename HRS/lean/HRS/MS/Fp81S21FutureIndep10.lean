import HRS.MS.Fp81S21FutureIndep5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2

/-- The full initial-plus-noise evaluation decomposes on the retained source
into the initial and cutoff-past part and the cutoff-future part. -/
theorem fp81s21_combined_source_decomposition
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
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
    (r t : ℝ) (φ : Euc p.d → ℝ) :
    ∀ᵐ ω ∂P, W (J (fp81s21_combinedFeature p R hK t φ)) ω =
      W (J (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
        movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ))) ω +
      W (J (fp81s21_futureNoiseSourceFeature p R r t φ)) ω := by
  have hfeature :
      (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
        movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ) :
          Fp81S21GaussFeatureHilbert p R) +
        fp81s21_futureNoiseSourceFeature p R r t φ =
          fp81s21_combinedFeature p R hK t φ := by
    apply WithLp.ofLp_injective
    simp [fp81s21_combinedFeature, fp81s21_futureNoiseSourceFeature]
  have h := fp81s21_source_add_ae P W hWm hW2 hcomb
    (J (WithLp.toLp 2 (fp81s21_initialGaussianFeature p R hK t φ,
      movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ)))
    (J (fp81s21_futureNoiseSourceFeature p R r t φ))
  simpa only [← map_add, hfeature] using h

#print axioms fp81s21_combined_source_decomposition

end HRS.Fp81.S21
end
