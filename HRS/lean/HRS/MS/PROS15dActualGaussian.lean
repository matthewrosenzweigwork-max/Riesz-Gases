import HRS.MS.PROS15dJointGaussian

/-!
# R26-T3.S15d: Gaussian finite spectral vectors for the actual HS tilt

The genuine infinite Hilbert–Schmidt quadratic witness is jointly compatible
with every finite spectral-vector Gaussian law, including the exact reciprocal
variance formula. This is not yet the physical all-test S15d theorem.
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_actual_tilt_finite_spectral_gaussian
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j => lam j ^ 2))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Q : Ω → ℝ,
      HRS.TendstoL2 P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n, lam j * (ξ j ω ^ 2 - 1)) Q ∧
      ∀ n : ℕ, HRS.IsCenteredGaussian
        ((r26t3_tilt P (fun ω => γ * Q ω)).map
          (fun ω (i : Fin n) => ξ i ω)) := by
  obtain ⟨Q, hT, _, _, hLaw⟩ :=
    r26t3_hs_gaussian_tilt P ξ hξ lam hlam hlam2 γ hγ
  refine ⟨Q, hT, ?_⟩
  intro n
  change HRS.IsCenteredGaussian (law (r26t3_tilt P (fun ω => γ * Q ω))
      (fun ω (i : Fin n) => ξ i ω))
  rw [hLaw n]
  exact s15d_centered_gaussian_product n
    (fun i : Fin n => Real.toNNReal ((1 + γ * lam i)⁻¹))

end HRS.MS.R26T3
