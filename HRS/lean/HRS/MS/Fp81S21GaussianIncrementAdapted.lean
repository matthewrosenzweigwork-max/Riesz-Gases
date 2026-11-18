import HRS.MS.Fp81S21GaussianPredictionAdapted2
import HRS.MS.Fp81S21GaussianPhysicalPackage

/-! Packet 36, fixed-time adaptation of the supplied thermal and half-Wick
operators. The sigma-algebra is the exact retained source past, and all limits
are taken in closed subspaces of the ambient L² space. In particular no new
thermal operator, quadratic family, chart, or Gaussian source is selected.
This file is a partial producer: it does not assert adaptation of time integrals
or the finite approximations of the actual cumulative increments. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

private theorem fp81s21_increment_past_le
    (Q : fp81s21_Gaussian35Selection p R) (v : ℝ) :
    MeasurableSpace.comap (fp81s21_predictionPast Q v) inferInstance ≤
      Q.src.G0.mΩ := by
  exact (measurable_pi_iff.2 fun i => Q.src.rawBundle.2.2.2.1 _).comap_le

private theorem fp81s21_increment_noise_supported
    (u v : ℝ) (huv : u ≤ v) (φ : Euc p.d → ℝ) :
    movingNoiseFeature R 0 u φ ∈ fp81s21_PastNoiseFeatures p.d v := by
  unfold movingNoiseFeature
  split_ifs with hm
  · filter_upwards [hm.coeFn_toLp] with q hq
    intro hvq
    rw [hq]
    have hn : q.1 ∉ Icc (0 : ℝ) u := fun h =>
      (not_lt_of_ge (h.2.trans huv)) hvq
    simp only [movingNoiseKernel, if_neg hn]
  · filter_upwards [Lp.coeFn_zero (Euc p.d) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d)))] with q hq
    intro _
    exact hq

private theorem fp81s21_increment_oscillator_adapted
    (Q : fp81s21_Gaussian35Selection p R) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (φ : Euc p.d → ℝ) (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    AEStronglyMeasurable[MeasurableSpace.comap (fp81s21_predictionPast Q v) inferInstance]
      (fun ω => OscDual.eval (Q.src.G0.Z u ω) φ) Q.src.G0.P := by
  letI := fp81s21_initialMeasure_isProbability p R
  let b : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d v :=
    (fp81s21_initialGaussianFeature p R Q.src.hK u φ,
      ⟨movingNoiseFeature R 0 u φ, fp81s21_increment_noise_supported u v huv φ⟩)
  have hm : Measurable[MeasurableSpace.comap (fp81s21_predictionPast Q v) inferInstance]
      (fun ω => fp81s21_predictionPast Q v ω b) :=
    (measurable_pi_apply b).comp (comap_measurable (fp81s21_predictionPast Q v))
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr
    (Q.src.sourceEvaluation u hu φ hφ).symm

/-- Every evaluation of the supplied thermal operator before the cutoff is
measurable in the retained source past. Density is used in thermal L², and
closedness in ambient probability L²; no radius or replacement operator is needed. -/
theorem fp81s21_gaussian_thermal_past_adapted
    (Q : fp81s21_Physical35 p R) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance]
      (Q.S.T Q.src.G0 u f : Q.src.G0.Ω → ℝ) Q.src.G0.P := by
  let m := MeasurableSpace.comap
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  have hm : m ≤ Q.src.G0.mΩ := fp81s21_increment_past_le _ v
  have hc : IsClosed {f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) |
      AEStronglyMeasurable[m] (Q.S.T Q.src.G0 u f : Q.src.G0.Ω → ℝ) Q.src.G0.P} :=
    (isClosed_aestronglyMeasurable (F := ℝ) (μ := Q.src.G0.P) (p := (2 : ℝ≥0∞)) hm).preimage
      (Q.S.T Q.src.G0 u).continuous
  apply closure_minimal (t := {f : Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) |
    AEStronglyMeasurable[m] (Q.S.T Q.src.G0 u f : Q.src.G0.Ω → ℝ) Q.src.G0.P})
    ?_ hc (fp81s21_gaussianSourceSpace_oscTest_dense p R f)
  rintro _ ⟨φ, rfl⟩
  exact (fp81s21_increment_oscillator_adapted Q.tofp81s21_Gaussian35Selection
    u v hu huv φ.1 φ.2).congr
      (Q.T_oscillator u hu φ.1 φ.2
        (fp81s21_gaussianSourceSpace_oscTest_memLp p R φ)).symm

private theorem fp81s21_increment_sum_adapted
    {Ω ι : Type*} {m m0 : MeasurableSpace Ω} {P : @Measure Ω m0}
    (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, AEStronglyMeasurable[m] (f i) P) :
    AEStronglyMeasurable[m] (fun ω => ∑ i ∈ s, f i ω) P := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (aestronglyMeasurable_const : AEStronglyMeasurable[m] (fun _ : Ω => (0 : ℝ)) P)
  | @insert i s hi ih =>
    intro hf
    simpa only [Finset.sum_insert hi, Pi.add_def] using
      (hf i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The actual supplied half-Wick operator is past-adapted on every product
kernel. Its finite centered products retain the factor one half; symmetrization
and density then identify the limit with this same operator. -/
theorem fp81s21_gaussian_halfWick_past_adapted
    (Q : fp81s21_Physical35 p R) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (k : Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
      (HRS.Whole.withDensityReal R.ρβ))) :
    AEStronglyMeasurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance]
      (Q.S.W Q.src.G0 u k : Q.src.G0.Ω → ℝ) Q.src.G0.P := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let m := MeasurableSpace.comap
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) inferInstance
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  have hm : m ≤ Q.src.G0.mΩ := fp81s21_increment_past_le _ v
  let A : Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
    (lpMeas ℝ ℝ m 2 Q.src.G0.P).comap (Q.S.W Q.src.G0 u).toLinearMap
  have hc : IsClosed (A : Set (Lp ℝ 2 (μ.prod μ))) :=
    (isClosed_aestronglyMeasurable (F := ℝ) (μ := Q.src.G0.P) (p := (2 : ℝ≥0∞)) hm).preimage
      (Q.S.W Q.src.G0 u).continuous
  obtain ⟨hL, hJ, hW⟩ := Q.supplied_half_wick u hu
  have hgen : fp81s21_wickB32_generators μ ⊆ A := by
    rintro _ ⟨n, c, φ, hdata, hk, rfl⟩
    have hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i) :=
      fun i => fp81s21_isOscTest_of_r2 hdata i
    have heq := fp81s21_wickFam_oscillator_finite_rank R Q.src.G0
      (Q.S.T Q.src.G0 u) Q.S.Kstar hL hJ φ hφ c hk
    rw [← hW] at heq
    change AEStronglyMeasurable[m] _ Q.src.G0.P
    apply AEStronglyMeasurable.congr _ heq.symm
    unfold fp81s21_wickG_finite_rank_polynomial
    have ht := fun f : Lp ℝ 2 μ => fp81s21_gaussian_thermal_past_adapted Q u v hu huv f
    apply AEStronglyMeasurable.mul aestronglyMeasurable_const
    apply fp81s21_increment_sum_adapted
    intro i _
    apply fp81s21_increment_sum_adapted
    intro j _
    exact aestronglyMeasurable_const.mul
      (((ht _).mul (ht _)).sub aestronglyMeasurable_const)
  have hspan : fp81s21_wickB32_finiteRankSubmodule μ ≤ A :=
    Submodule.span_le.mpr hgen
  have hs : fp81s21_wickB23_symmetrize μ k ∈ A :=
    closure_minimal hspan hc (fp81s21_wickB33_symmetric_mem_closure μ _
      (fp81s21_wickB23_symmetrize_idempotent μ k))
  have hsym : Q.S.W Q.src.G0 u k =
      Q.S.W Q.src.G0 u (fp81s21_wickB23_symmetrize μ k) := by
    rw [hW]
    exact fp81s21_wickB311_operator_symmetrize (Q.S.T Q.src.G0 u) Q.S.Kstar hL hJ k
  change AEStronglyMeasurable[m] _ Q.src.G0.P
  rw [hsym]
  exact hs

#print axioms fp81s21_gaussian_thermal_past_adapted
#print axioms fp81s21_gaussian_halfWick_past_adapted
end HRS.Fp81.S21
end
