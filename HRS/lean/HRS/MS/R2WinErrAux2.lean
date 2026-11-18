import HRS.MS.R2WinErrAux1

/-!
# S10.4 packet E2a: the pathwise covariance error for a general feature family

`s104_trace_pathwise`: for a density `ρ ≤ Λ` with finite second moment, a collision-free configuration, the covariation forms
`B₁, B₂` of the empirical measure and of `ρ dx` built from ANY feature family `Γ_a ∈ C^{m_*-1}(ℝ^d; K)` with derivative bounds
`≤ B` (the scale `B = C θ_b(r)` of the window feature enters only through `B^2`):
`‖B₁ - B₂‖₁ ≤ C_p q B² [R^{d/2}(N^{-1/d} + (F_N + o_N)^{1/2}) + (⟨|x|²,μ_N⟩ + ⟨|x|²,ρ⟩)/R²]`.
This is `s56_trace_pathwise` with the feature family and its bound as inputs (no `WholeSetup`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.R2WinErr

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.GenPath

variable {d : ℕ}

theorem s104_trace_pathwise (hd1 : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min Cp : ℝ, 0 ≤ Cp ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (m T q : ℝ), 0 ≤ q → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → Integrable (fun x => ‖x‖ ^ 2 * ρ x) →
      ∀ X : EucConfig d N, Function.Injective X → ∀ R : ℝ, 1 ≤ R →
      ∀ (Γ : Fin d → Euc d → KSpace d m T) (B : ℝ),
      (∀ a, ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) (Γ a)) →
      (∀ a, ∀ j ≤ mStar d - 1, ∀ x, ‖iteratedFDeriv ℝ j (Γ a) x‖ ≤ B) →
      ∀ B₁ B₂ : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      (∀ u v, B₁ u v = featureForm m T q Γ (HRS.Whole.empirical X) u v) →
      (∀ u v, B₂ u v = featureForm m T q Γ (HRS.Whole.withDensityReal ρ) u v) →
      HRS.traceNormForm (B₁ - B₂) ≤ Cp * q * B ^ 2 *
        (R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oN d s C₀ N)) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2) := by
  obtain ⟨C₀p, C₁, hC₀p, hpair⟩ := HRS.MH.CoercTest.p_assembly d hd1 s hs0 hsd
  obtain ⟨χ, hχ⟩ := HRS.MS.Ul.ul0_exists_ulocCutoff d
  obtain ⟨Ct, hCt⟩ := test_cutoff_pathwise hd1 s hs0 hsd χ hχ C₁
  obtain ⟨Cn, hCn0, hCnb⟩ := s56_cNormE_le hχ
  set Λ₁ : ℝ := max Λ 1 with hΛ₁
  have hΛ₁1 : 1 ≤ Λ₁ := le_max_right _ _
  set Cc : ℝ := max Ct 0 with hCcdef
  refine ⟨C₀p * Λ₁ ^ (s / d) + Real.log Λ₁ / (2 * d),
    2 * d * (Cc * (Cn * 2 ^ (mStar d - 1))), by positivity, fun C₀ hC0 m T q hq N hN ρ hprob hρΛ hmom X hX R hR
    Γ B hΓ hB B₁ B₂ h1 h2 => ?_⟩
  haveI : IsProbabilityMeasure (HRS.Whole.empirical X) := HRS.Whole.empirical_isProbabilityMeasure (by omega) X
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q09A.measure_isProb hprob
  have hρle : ∀ x, ρ x ≤ Λ₁ := fun x => (hρΛ x).trans (le_max_left _ _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  set Err : ℝ := R ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 : ℝ) / d) +
            Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oN d s C₀ N)) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2 with hErr
  have hRpos : 0 < R := by linarith
  have hErr0 : 0 ≤ Err := by
    have := s56_secondMoment_nonneg (HRS.Whole.empirical X)
    have := s56_secondMoment_nonneg (HRS.Whole.withDensityReal ρ)
    positivity
  have hTest : ∀ h : Euc d → ℝ, cNormE χ h < ⊤ →
      abs (HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h) ≤ Cc * (cNormE χ h).toReal * Err := by
    intro h hh
    have key := hCt C₀p (hpair C₀p le_rfl) Λ₁ hΛ₁1 N hN ρ hprob hρle hmom X hX h hh R hR
    refine key.trans ?_
    have hsm : HRS.smearScale d N Λ₁ ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
      unfold HRS.smearScale
      exact Real.rpow_le_rpow_of_nonpos hNpos (by nlinarith) (by
        have : (0 : ℝ) ≤ 1 / d := by positivity
        rw [neg_div]; linarith)
    have hon : HRS.oNΛ d s C₀p Λ₁ N ≤ HRS.oN d s C₀ N := s56_oNL_le hd1 hΛ₁1 hC0 N hN
    have hsq : Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀p Λ₁ N) ≤
        Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oN d s C₀ N) :=
      Real.sqrt_le_sqrt (by linarith)
    have hE1 : R ^ ((d : ℝ) / 2) * (HRS.smearScale d N Λ₁ + Real.sqrt (rieszModulatedEnergy d s X
          (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀p Λ₁ N)) +
        (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2 ≤ Err := by
      rw [hErr]; gcongr
    have hE0 : 0 ≤ R ^ ((d : ℝ) / 2) * (HRS.smearScale d N Λ₁ + Real.sqrt (rieszModulatedEnergy d s X
          (HRS.Whole.withDensityReal ρ) + HRS.oNΛ d s C₀p Λ₁ N)) +
        (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2 := by
      have := s56_secondMoment_nonneg (HRS.Whole.empirical X)
      have := s56_secondMoment_nonneg (HRS.Whole.withDensityReal ρ)
      have : 0 ≤ HRS.smearScale d N Λ₁ := by unfold HRS.smearScale; positivity
      positivity
    have hnn : 0 ≤ (cNormE χ h).toReal := ENNReal.toReal_nonneg
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn) hE1 hE0
      (mul_nonneg (le_max_right _ _) hnn)
  have hgen := s56_trace_generic (d := d) (χ := χ) (Cn := Cn) hCn0 hCnb Γ B hΓ hB (HRS.Whole.empirical X)
    (HRS.Whole.withDensityReal ρ) (Cc := Cc) (Err := Err) (le_max_right _ _) hErr0 hTest hq B₁ B₂ h1 h2
  refine hgen.trans (le_of_eq ?_)
  ring

end HRS.MS.R2WinErr
