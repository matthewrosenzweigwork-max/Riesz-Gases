import HRS.Main.ThermLinAux1
import HRS.Main.ThermLinAux4

/-!
# THERMLIN: relocated proofs of the existence rows of `HRS/Main/Headline.lean`

RELOCATION PATTERN: the frozen statements of `HRS/Main/Headline.lean` are not edited; each proved one is restated
VERBATIM here as `<name>_proof` and tied by `example := (@<name>_proof : type_of% @HRS.Main.<name>)`.

* `preparedGaussian_exists_proof` (Prop. 5.9 / `exists_iid_gaussian_field` for `β₀ = 0`; for `β₀ > 0` the
  response operator of `ResponseAux`, `ThermLinAux1`).
* `preparedLinear_exists_proof` (Prop. A.33 at level `m` with continuous paths: Gaussian Hilbert martingale +
  stochastic convolution against the dual evolution; `ThermLinAux2-4`; uses `T25PAux9`, `T25PAux11` of branch wk/t25).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem preparedGaussian_exists_proof (S : PreparedData d) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) :
    ∃ ν : Measure (NegSobolev d m), IsProbabilityMeasure ν ∧
      IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) := by
  haveI hμ0 : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
  by_cases h0 : β₀ = 0
  · have hc : preparedCov d S.s β₀ S.μ0 = iidCov S.μ0 := by
      funext φ ψ
      simp [preparedCov, h0]
    rw [hc]
    exact exists_iid_gaussian_field m hm S.μ0
  · have hc : preparedCov d S.s β₀ S.μ0 = susceptibilityCov (periodicRiesz d S.s) S.μ0 β₀ := by
      funext φ ψ
      simp [preparedCov, h0]
    rw [hc]
    have hcont : Continuous S.ρ0 := HRS.StaticLimitAux.continuous_of_smooth S.hρ0.smooth
    obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
    have hΛ : ∀ x, S.ρ0 x ≤ S.ρ0 x0 := fun x => hx0 (Set.mem_univ x)
    have h0' : ∀ n : Lattice d, 0 ≤ rieszCoeff d S.s n := fun n => by
      by_cases hn : n = 0
      · simp [rieszCoeff, hn]
      · exact (rieszCoeff_pos S.hd S.hs0 S.hsd n hn).le
    obtain ⟨g', hgg, hS⟩ := HRS.ResponseAux.setup_of_kernel (integral_periodicRiesz S.hd S.hs0 S.hsd).1
      (rieszCoeff d S.s) h0'
      (HRS.ResponseAux.hcoef_of_funFourierCoeff (periodicRiesz_fourierCoeff S.hd S.hs0 S.hsd))
      S.hρ0.density hΛ
    exact HRS.ThermLin.thermlin_exists_gauss_kernel hS hgg (lt_of_le_of_ne hβ₀ (Ne.symm h0)).le m
      (by linarith)

example := (@preparedGaussian_exists_proof : type_of% @HRS.Main.preparedGaussian_exists)

theorem preparedLinear_exists_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T' : ℝ)
    (hT' : 0 < T') (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν] :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
      IsPreparedLinear S m T' ν P' Y₀ Y :=
  HRS.ThermLin.thermlin_preparedLinear_exists S m hm T' hT' ν

example := (@preparedLinear_exists_proof : type_of% @HRS.Main.preparedLinear_exists)

end Main

end HRS
