import HRS.MS.GenPathAux25

/-!
# S5.6 packet P7d: measurability of `x ↦ k₀(x)`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56F_integrable (C : WholeCoeff d) (m T Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z)
    (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf)
    (ν μρ : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μρ]
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μρ) :
    Integrable (s56F C m T) (ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine Integrable.mono' (g := fun p => d * Bf * (‖p.1‖ + ‖p.2.1‖)) ?_
    (s56F_meas C m T hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => s56F_norm_le C m T Bf hBf hbd p)
  refine Integrable.const_mul ?_ _
  exact (hν.comp_fst _).add ((hμ.comp_fst _).comp_snd ν)

/-- The `k₀` of the empirical measure of a configuration is the average over the particles. -/
theorem s56_k0_emp (C : WholeCoeff d) (m T σ Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z)
    (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf)
    {N : ℕ} (hN : 0 < N) (μρ : Measure (Euc d)) [IsProbabilityMeasure μρ]
    (hμ : Integrable (fun x : Euc d => ‖x‖) μρ) (x : EucConfig d N) :
    s56k0 C m T σ (HRS.Whole.empirical x) μρ = σ • ((N : ℝ)⁻¹ • ∑ i : Fin N,
      ∫ q : Euc d × ℝ, s56F C m T (x i, q) ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure hN x
  have hν : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical x) := HRS.Whole.Q09A.integrable_empirical hN x _
  have hint := s56F_integrable C m T Bf hBf hmeas hbd (HRS.Whole.empirical x) μρ hν hμ
  unfold s56k0
  rw [integral_prod _ hint]
  congr 1
  unfold HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact integrable_dirac (by simp)

theorem s56_k0_meas (C : WholeCoeff d) (m T σ Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z)
    (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf)
    {N : ℕ} (hN : 0 < N) (μρ : Measure (Euc d)) [IsProbabilityMeasure μρ]
    (hμ : Integrable (fun x : Euc d => ‖x‖) μρ) :
    Measurable fun x : EucConfig d N => s56k0 C m T σ (HRS.Whole.empirical x) μρ := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  simp_rw [s56_k0_emp C m T σ Bf hBf hmeas hbd hN μρ hμ]
  have hg : StronglyMeasurable fun z : Euc d => ∫ q : Euc d × ℝ, s56F C m T (z, q)
      ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (s56F_meas C m T hmeas).stronglyMeasurable.integral_prod_right'
  have hsum : Measurable fun x : EucConfig d N => ∑ i : Fin N, ∫ q : Euc d × ℝ, s56F C m T (x i, q)
      ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    Finset.measurable_sum (Finset.univ : Finset (Fin N)) fun i _ => hg.measurable.comp (measurable_pi_apply i)
  exact (hsum.const_smul ((N : ℝ)⁻¹)).const_smul σ

end HRS.MS.GenPath
