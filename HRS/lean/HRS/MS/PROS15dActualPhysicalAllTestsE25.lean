import HRS.MS.PROS15dCenteredPhysicalTestsE25
import HRS.MS.PROS15dPhysicalRieszProjectionP21

/-!
# R26-T3.S15d: actual physical Riesz Gaussianity for *every centered spatial test*

The Gaussian field, its physical eigenfunctions and its diagonal HS Wick
quadratic are the genuine frozen ProductGaussian objects. No extra
spectral-approximation hypothesis is imposed. This does not yet identify
the frozen canonical Wick representative or susceptibility covariance.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_every_centered_test_gaussian
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
        HRS.Whole.MemL2Zero (r26t3_mu R 0) f →
        HRS.IsCenteredGaussian
          ((r26t3_tilt I.P (fun ω => γ * Q ω)).map (I.η f)) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, Q, he, b, hlam, _hon, hs, _hkernel,
      hQ, hExp1, hExp2, hLaw, hb, _hTail⟩ :=
    s15d_physical_riesz_alltest_spectral_tilt_projection
      hδ hδh R I γ hγ
  refine ⟨lam, e, Q, (fun j => ⟨hlam j, he j⟩),
    hs, hQ, hExp1, hExp2, ?_⟩
  let W : I.Ω → ℝ := fun ω => γ * Q ω
  have hW : AEMeasurable W I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hExp1' : Integrable
      (fun ω => Real.exp (-W ω)) I.P := by
    simpa only [W, neg_mul] using hExp1
  have hExp2' : Integrable
      (fun ω => Real.exp (-(2 * W ω))) I.P := by
    convert hExp2 using 1
    funext ω
    simp only [W]
    ring
  have hFinite : ∀ (n : ℕ) (a : Fin n → ℝ),
      HRS.IsCenteredGaussian
        ((r26t3_tilt I.P W).map
          (I.η (fun x => ∑ j : Fin n, a j * e j x))) := by
    intro n a
    exact s15d_physical_finite_span_tilted_gaussian
      I W hW hExp1' e (fun j => (he j).1) n
      (fun j => ((1 + γ * lam j)⁻¹).toNNReal)
      (by simpa only [W, HRS.law] using hLaw n) a
  intro f hf
  exact s15d_hilbert_spectral_tilted_centered_test_gaussian
    I W hW hExp1' hExp2' e
    (fun j => (he j).1) b hb hFinite f hf

#print axioms s15d_physical_riesz_every_centered_test_gaussian
end HRS.MS.R26T3
