import HRS.MS.Fp81S21FutureIndep30

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2 HRS.MS.GenPath

/-- The propagated initial-and-noise Gaussian functional is measurable in the
complete retained past at the absolute cutoff. -/
theorem fp81s21_propagated_source_past_measurable
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ} {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {Ω : Type*} [MeasurableSpace Ω]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hrt : r ≤ t) {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    Measurable[MeasurableSpace.comap
      (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
        W (J (WithLp.toLp 2 (i.1, i.2.1))) ω) inferInstance]
      (fun ω => W (J (fp81s21_combinedFeature p R hK r
        (propagatorW (r26t3_coeff R) r t φ))) ω) := by
  let past := fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
    W (J (WithLp.toLp 2 (i.1, i.2.1))) ω
  let i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r :=
    (fp81s21_initialGaussianFeature p R hK t φ,
      ⟨movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ,
        fp81s21_past_feature_supported p R hδ hδhalf hH hr ht hφ⟩)
  have hm : Measurable[MeasurableSpace.comap past inferInstance] (fun ω => past ω i) :=
    (measurable_pi_apply i).comp (comap_measurable past)
  rw [fp81s21_propagated_combined_feature p R hδ hδhalf hH hK hr ht hrt hφ]
  exact hm

#print axioms fp81s21_propagated_source_past_measurable
end HRS.Fp81.S21
end
