import HRS.Main.ThermLinFinal
import HRS.Main.HeadlineEdgeworth

/-!
# Packet E214A, lemma 1: non-vacuity of the Gaussian antecedents of `IsWindowEdgeworth.expansion`

`e214_exists_gaussian`: for every `a ≥ 0`, `T > 0` there are a centered Gaussian `ν` with the prepared covariance
and a realisation `IsPreparedLinear S m (a + T) ν P' Z₀ Z`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214A

open HRS HRS.Main

variable {d : ℕ}

theorem e214_exists_gaussian (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∃ ν : Measure (NegSobolev d m), IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z := by
  have hm1 : (d : ℝ) + 2 < m := by
    have := hE.m_gt
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm2 : (d : ℝ) / 2 < m := by
    have := hE.m_gt
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ν, hν, hG⟩ := preparedGaussian_exists_proof S β₀ hE.β₀_nonneg m hm2
  haveI := hν
  obtain ⟨Ω', hΩ', P', hP', Z₀, Z, hZ⟩ := preparedLinear_exists_proof S m hm1 (a + T) (by linarith) ν
  exact ⟨ν, hG, Ω', hΩ', P', hP', Z₀, Z, hZ⟩

end HRS.MC.E214A

end
