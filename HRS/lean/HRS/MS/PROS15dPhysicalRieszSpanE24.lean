import HRS.MS.PROS15dPhysicalSpanE24
import HRS.MS.PROS15dPhysicalRieszTilt

/-!
# S15d: exact finite *physical spatial* Gaussian laws for the Riesz spectral family

This takes the actual Hilbert--Schmidt spectral quadratic and the actual
ProductGaussian first-chaos field on the same probability space. Every
finite spatial combination of the physical Riesz eigenfunctions, including
arbitrary coefficients and zero modes, has a centered Gaussian law under
the genuine normalized quadratic tilt.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_finite_spatial_span_gaussian
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ) (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      Summable (fun j => lam j ^ 2) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * (I.η (e j) ω ^ 2 - 1)) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) I.P ∧
      ∀ (n : ℕ) (a : Fin n → ℝ),
        HRS.IsCenteredGaussian
          ((r26t3_tilt I.P (fun ω => γ * Q ω)).map
            (I.η (fun x => ∑ j : Fin n, a j * e j x))) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, Q, he, _hon, hs, _hKernel, hQ, hInt, hLaw⟩ :=
    s15d_physical_riesz_spectral_tilt hδ hδh R I γ hγ
  refine ⟨lam, e, Q, he, hs, hQ, hInt, ?_⟩
  intro n a
  have hV : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hIntPrime :
      Integrable (fun ω => Real.exp (-(γ * Q ω))) I.P := by
    simpa only [neg_mul] using hInt
  exact s15d_physical_finite_span_tilted_gaussian
    I (fun ω => γ * Q ω) hV hIntPrime e
    (fun j => (he j).2.1) n
    (fun j => ((1 + γ * lam j)⁻¹).toNNReal)
    (by simpa only [HRS.law] using hLaw n) a

#print axioms s15d_physical_riesz_finite_spatial_span_gaussian
end HRS.MS.R26T3
