import HRS.MS.PROS15dActualPhysicalAllTestsE25
import HRS.MS.R2ChaosAux7
import HRS.MS.S21T4ProdF

/-!
# S15d: every original physical Riesz test has a centered Gaussian tilted law

The original smooth test need not be centered. Its physical Gaussian
observable equals that of its centered projection almost everywhere under
the SAME normalized HS exponential tilt. No covariance identification is
claimed.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_all_R2_tests_gaussian
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    letI : IsProbabilityMeasure (r26t3_mu R 0) :=
      s21h2_mu_prob hδ hδh R
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ)
      (Q : I.Ω → ℝ),
      (∀ j, 0 ≤ lam j ∧ HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j)) ∧
      Summable (fun j => lam j ^ 2) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * (I.η (e j) ω ^ 2 - 1)) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) I.P ∧
      Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) I.P ∧
      ∀ (f : HRS.Euc p.d → ℝ),
        HRS.Whole.IsR2Test f →
        HRS.IsCenteredGaussian
          ((r26t3_tilt I.P (fun ω => γ * Q ω)).map (I.η f)) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, Q, he, hs, hQ, hExp1, hExp2, hG⟩ :=
    s15d_physical_riesz_every_centered_test_gaussian
      hδ hδh R I γ hγ
  refine ⟨lam, e, Q, he, hs, hQ, hExp1, hExp2, ?_⟩
  have hW : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hPtAC : r26t3_tilt I.P (fun ω => γ * Q ω) ≪ I.P := by
    unfold r26t3_tilt
    intro s hs0
    simp [withDensity_absolutelyContinuous I.P _ hs0]
  intro f hf
  have hfc : HRS.Whole.MemL2Zero (r26t3_mu R 0)
      (HRS.Whole.projMean (r26t3_mu R 0) f) :=
    ⟨HRS.MS.R2Chaos.s94_memLp_projMean hf,
     HRS.MS.R2Chaos.s94_integral_projMean hf⟩
  have hGc := hG (HRS.Whole.projMean (r26t3_mu R 0) f) hfc
  have hEq : I.η (HRS.Whole.projMean (r26t3_mu R 0) f)
      =ᵐ[I.P] I.η f :=
    s21l_eta_test (s21t4_product_eta_bundle I) hf
  have hEqPt := hPtAC hEq
  rw [← Measure.map_congr hEqPt]
  exact hGc

#print axioms s15d_physical_riesz_all_R2_tests_gaussian
end HRS.MS.R26T3
