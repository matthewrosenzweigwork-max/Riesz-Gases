import HRS.MS.PROS15dFiniteLinearGaussian
import HRS.MS.PROS15dPhysicalRieszTilt

/-!
# S15d: Gaussian laws of arbitrary finite linear combinations of physical
# Riesz spectral coordinates under their actual Hilbert--Schmidt tilt

The spectral data are obtained unconditionally from the physical Riesz
trajectory. The tilted measure and every observable live on the original
ProductGaussian space. Singular linear transformations and zero modes are
allowed. This is an approximation ingredient for the frozen arbitrary-test
S15d theorem; it does not identify the prescribed Wick source.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_linear_spectral_gaussian
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ)
      (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      Summable (fun j => lam j ^ 2) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * (I.η (e j) ω ^ 2 - 1)) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) I.P ∧
      ∀ (n m : ℕ)
        (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)),
        HRS.IsCenteredGaussian
          ((r26t3_tilt I.P (fun ω => γ * Q ω)).map
            (fun ω => A (fun i : Fin n => I.η (e i) ω))) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, Q, he, _hon, hsum, _hKernel, hQ, hInt, hLaw⟩ :=
    s15d_physical_riesz_spectral_tilt hδ hδh R I γ hγ
  let Pt := r26t3_tilt I.P (fun ω => γ * Q ω)
  have hV : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hIntPrime : Integrable (fun ω => Real.exp (-(γ * Q ω))) I.P := by
    simpa only [neg_mul] using hInt
  letI : IsProbabilityMeasure Pt :=
    r26t3_tilt_isProb I.P hV hIntPrime
  have hAC : Pt ≪ I.P := by
    unfold Pt r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous I.P _ hs]
  refine ⟨lam, e, Q, he, hsum, hQ, hInt, ?_⟩
  intro n m A
  have hX : ∀ i : Fin n, AEMeasurable (I.η (e i)) Pt :=
    fun i => (I.meas (e i) (he i).2.1).aemeasurable.mono_ac hAC
  have hv : Pt.map (fun ω (i : Fin n) => I.η (e i) ω) =
      Measure.pi (fun i : Fin n =>
        gaussianReal 0 (Real.toNNReal ((1 + γ * lam i)⁻¹))) := by
    simpa only [Pt, HRS.law] using hLaw n
  exact s15d_finite_spectral_linear_gaussian
    (fun i : Fin n => I.η (e i)) hX
    (fun i : Fin n => Real.toNNReal ((1 + γ * lam i)⁻¹)) hv A

#print axioms s15d_physical_riesz_linear_spectral_gaussian
end HRS.MS.R26T3
