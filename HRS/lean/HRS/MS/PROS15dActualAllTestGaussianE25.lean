import HRS.MS.PROS15dSpatialProjectionE25
import HRS.MS.PROS15dPhysicalSpanE24
import HRS.MS.PROS15dTestGaussianBridgeC19

/-!
# S15d: all centered physical spatial L² tests have Gaussian laws under the
# actual Hilbert--Schmidt Riesz tilt

Unlike finite spectral-coordinate results, this quantifies over the
entire centered spatial L² space and constructs the approximation using
the complete Riesz eigenbasis. The Gaussian tilt is the same random
quadratic on the same frozen ProductGaussian probability space at every
approximation stage. This theorem alone does NOT identify the covariance
with the frozen susceptibility resolvent, nor the canonical Wick quadratic.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_all_centered_L2_gaussian
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
      ∀ v : s21h2_V (r26t3_mu R 0),
        HRS.IsCenteredGaussian
          ((r26t3_tilt I.P (fun ω => γ * Q ω)).map
            (I.η (fun x => (((v : s21h2_V (r26t3_mu R 0)) :
              Lp ℝ 2 (r26t3_mu R 0)) x)))) := by
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
  intro v
  let f : HRS.Euc p.d → ℝ :=
    fun x => (((v : s21h2_V (r26t3_mu R 0)) :
      Lp ℝ 2 (r26t3_mu R 0)) x)
  let u : ℕ → HRS.Euc p.d → ℝ := fun n x =>
    ∑ j ∈ Finset.range n, inner ℝ (b j) v * e j x
  have hf : MemLp f 2 (r26t3_mu R 0) := Lp.memLp _
  have hu : ∀ n, MemLp (u n) 2 (r26t3_mu R 0) := by
    intro n
    exact memLp_finsetSum _ (fun j _ => (he j).1.const_mul _)
  have hG : ∀ n, HRS.IsCenteredGaussian
      ((r26t3_tilt I.P W).map (I.η (u n))) := by
    intro n
    have h := s15d_physical_finite_span_tilted_gaussian
      I W hW hExp1' e (fun j => (he j).1) n
      (fun j => ((1 + γ * lam j)⁻¹).toNNReal)
      (by simpa only [W, HRS.law] using hLaw n)
      (fun j : Fin n => inner ℝ (b j) v)
    simpa only [u, Finset.sum_range] using h
  have hSpatial : Tendsto
      (fun n => ∫ x, (u n x - f x) ^ 2
        ∂(r26t3_mu R 0)) atTop (𝓝 0) := by
    simpa only [u, f] using
      s15d_physical_hilbert_spatial_projection_L2
        e (fun j => (he j).1) b hb v
  exact s15d_physical_tilted_gaussian_of_spatial_approximation
    I W hW hExp1' hExp2' f hf u hu hG hSpatial

#print axioms s15d_physical_riesz_all_centered_L2_gaussian
end HRS.MS.R26T3
