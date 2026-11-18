import HRS.MS.PROS15dSpectralCovariance

/-!
# R26-T3.S15d: exact covariance of the actual Hilbert–Schmidt Gaussian tilt

This specializes the general finite-coordinate covariance result to the
infinite Hilbert–Schmidt Gaussian quadratic witness supplied by S15c.
The remaining S15d work concerns identification of that witness with
the physical Wick chaos and passage from spectral to arbitrary tests.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_actual_spectral_covariance
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j => lam j ^ 2))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Q : Ω → ℝ,
      HRS.TendstoL2 P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n, lam j * (ξ j ω ^ 2 - 1)) Q ∧
      (∀ i j : ℕ,
        ∫ ω, ξ i ω * ξ j ω ∂(r26t3_tilt P (fun ω => γ * Q ω)) =
          if i = j then (Real.toNNReal ((1 + γ * lam i)⁻¹) : ℝ) else 0) := by
  classical
  obtain ⟨Q, hT, hint, hZ, hLaw⟩ :=
    r26t3_hs_gaussian_tilt P ξ hξ lam hlam hlam2 γ hγ
  let Pt := r26t3_tilt P (fun ω => γ * Q ω)
  have hlim := s21h2_s15c_inprob hξ lam hT γ 0
  have hVm : AEMeasurable (fun ω => γ * Q ω) P := hlim.aemeasurable_limit.snd
  have hint' : Integrable (fun ω => Real.exp (-(γ * Q ω))) P := by
    simpa only [neg_mul] using hint
  letI : IsProbabilityMeasure Pt := r26t3_tilt_isProb P hVm hint'
  have hac : Pt ≪ P := by
    unfold Pt r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous P _ hs]
  refine ⟨Q, hT, ?_⟩
  intro i j
  let n := max i j + 1
  let ii : Fin n := ⟨i, Nat.lt_succ_of_le (Nat.le_max_left i j)⟩
  let jj : Fin n := ⟨j, Nat.lt_succ_of_le (Nat.le_max_right i j)⟩
  have hm : ∀ k : Fin n, AEMeasurable (ξ k) Pt :=
    fun k => (hξ.aemeasurable k).mono_ac hac
  have hl : Pt.map (fun ω (k : Fin n) => ξ k ω) =
      Measure.pi (fun k : Fin n => gaussianReal 0
        (Real.toNNReal ((1 + γ * lam k)⁻¹))) := by
    simpa only [Pt] using hLaw n
  have hc := s15d_pi_gaussian_covariance (fun k : Fin n => ξ k) hm
    (fun k : Fin n => Real.toNNReal ((1 + γ * lam k)⁻¹)) hl ii jj
  by_cases hij : i = j <;> simpa [ii, jj, Pt, hij] using hc

end HRS.MS.R26T3
