import HRS.MS.Fp81S21RecentRSPhysical2

/-! Profile and expectation-rewriting steps for the supplied recent RS assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
namespace HRS.Fp81.S21

/-- The profile can be fixed before the particle number and supplied records. -/
theorem fp81s21_recentRS_profile_properties
    (KD KJ M : ℝ) (e : ℕ → ℝ)
    (hKD : 0 ≤ KD) (hKJ : 0 ≤ KJ)
    (he : ∀ N, 0 ≤ e N) (heT : Tendsto e atTop (𝓝 0)) :
    (∀ N, 0 ≤ (KD + KJ / 2) * (1 + Real.sqrt M) *
      (e N + 1 / ((N : ℝ) + 1))) ∧
    Tendsto (fun N : ℕ => (KD + KJ / 2) * (1 + Real.sqrt M) *
      (e N + 1 / ((N : ℝ) + 1))) atTop (𝓝 0) := by
  have hη : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · intro N
    have hEn : 0 ≤ e N := he N
    positivity
  · have hsum : Tendsto (fun N : ℕ => e N + 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
      simpa using heT.add hη
    simpa using hsum.const_mul ((KD + KJ / 2) * (1 + Real.sqrt M))

/-- Rewrite the four supplied values in the signed comparison. The value
identifications are intermediate inputs, proved for physical records by the
particle and Gaussian value theorems. -/
theorem fp81s21_recentRS_signed_of_values
    {Ω Ω' C D J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
    [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (yN : Ω → C) (dN : Ω → D) (jN : Ω → J)
    (yG : Ω' → C) (dG : Ω' → D) (jG : Ω' → J)
    (vDN vJN : Ω → ℝ) (vDG vJG : Ω' → ℝ)
    (hmN : Measurable (fun ω => (yN ω, (dN ω, jN ω))))
    (hmG : Measurable (fun ω => (yG ω, (dG ω, jG ω))))
    (hdN : MemLp dN 2 μ) (hjN : MemLp jN 2 μ)
    (hdG : MemLp dG 2 ν) (hjG : MemLp jG 2 ν)
    {KD KJ e M η : ℝ} (hKD : 0 < KD) (hKJ : 0 < KJ)
    (he : 0 ≤ e) (hM : 0 ≤ M) (hη : 0 < η)
    (FD : fp81s21_RecentRSKernel C D KD) (FJ : fp81s21_RecentRSKernel C J KJ)
    (hW : HRS.wassersteinE 2 (μ.map (fun ω => (yN ω, (dN ω, jN ω))))
      (ν.map (fun ω => (yG ω, (dG ω, jG ω)))) ≤ ENNReal.ofReal e)
    (hMoment : (∫ ω, (‖dG ω‖ ^ 2 + ‖jG ω‖ ^ 2) ∂ν) ≤ M)
    (hN : ∀ᵐ ω ∂μ, vDN ω = FD.kernel (yN ω) (dN ω) ∧
      vJN ω = FJ.kernel (yN ω) (jN ω))
    (hG : ∀ᵐ ω ∂ν, vDG ω = FD.kernel (yG ω) (dG ω) ∧
      vJG ω = FJ.kernel (yG ω) (jG ω)) :
    |fp81s21_recentRSCorrection (∫ ω, vDN ω ∂μ) (∫ ω, vJN ω ∂μ) -
      fp81s21_recentRSCorrection (∫ ω, vDG ω ∂ν) (∫ ω, vJG ω ∂ν)| ≤
      (KD + KJ / 2) * (1 + Real.sqrt M) * (e + η) := by
  have hDN := integral_congr_ae (hN.mono fun _ h => h.1)
  have hJN := integral_congr_ae (hN.mono fun _ h => h.2)
  have hDG := integral_congr_ae (hG.mono fun _ h => h.1)
  have hJG := integral_congr_ae (hG.mono fun _ h => h.2)
  rw [hDN, hJN, hDG, hJG]
  exact fp81s21_recentRS_joint_signed_comparison μ ν yN dN jN yG dG jG
    hmN hmG hdN hjN hdG hjG hKD hKJ he hM hη FD FJ hW hMoment

#print axioms fp81s21_recentRS_profile_properties
#print axioms fp81s21_recentRS_signed_of_values
end HRS.Fp81.S21
