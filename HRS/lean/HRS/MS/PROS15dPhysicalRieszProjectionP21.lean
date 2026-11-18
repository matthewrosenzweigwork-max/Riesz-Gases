import HRS.MS.PROS15dProjectionBasisP21
import HRS.MS.PROS15dTiltSquare
import HRS.MS.PROS15dPhysicalSpectralStd

/-!
# S15d: physical Riesz spectral projections under the actual Gaussian tilt

The complete orthonormal spectral family from S14a is realized as a
Hilbert basis of the centered spatial L² space. Its actual first-chaos
projection tails converge in tilted mean square for every centered
physical L² test. The spectral quadratic and doubled exponential moment
are constructed on the same frozen ProductGaussian probability space.

This is an unconditional intermediate theorem, not the original
susceptibility statement.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_physical_riesz_alltest_spectral_tilt_projection
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (I : ProductGaussian (r26t3_mu R 0))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    letI : IsProbabilityMeasure (r26t3_mu R 0) :=
      s21h2_mu_prob hδ hδh R
    ∃ (lam : ℕ → ℝ) (e : ℕ → HRS.Euc p.d → ℝ)
      (Q : I.Ω → ℝ)
      (he : ∀ j, HRS.Whole.MemL2Zero (r26t3_mu R 0) (e j))
      (b : HilbertBasis ℕ ℝ (s21h2_V (r26t3_mu R 0))),
      (∀ j, 0 ≤ lam j) ∧
      (∀ i j, ∫ x, e i x * e j x ∂(r26t3_mu R 0) =
        if i = j then 1 else 0) ∧
      Summable (fun j => lam j ^ 2) ∧
      Tendsto (fun n => eLpNorm (fun z : HRS.Euc p.d × HRS.Euc p.d =>
        HRS.Whole.r2CenterKernel (r26t3_mu R 0)
          (fun x y => HRS.Whole.rieszKernel p.d p.s (x-y)) z.1 z.2 -
          ∑ j ∈ Finset.range n, lam j * e j z.1 * e j z.2) 2
        ((r26t3_mu R 0).prod (r26t3_mu R 0))) atTop (𝓝 0) ∧
      HRS.TendstoL2 I.P (fun n ω =>
        (1/2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * ((I.η (e j) ω)^2-1)) Q ∧
      Integrable (fun ω => Real.exp (-γ*Q ω)) I.P ∧
      Integrable (fun ω => Real.exp (-(2*γ)*Q ω)) I.P ∧
      (∀ n, HRS.law (r26t3_tilt I.P (fun ω => γ * Q ω))
        (fun ω (j : Fin n) => I.η (e j) ω) =
        Measure.pi (fun j : Fin n =>
          gaussianReal 0 ((1 + γ * lam j)⁻¹).toNNReal)) ∧
      (∀ j, ((b j : s21h2_V (r26t3_mu R 0)) : Lp ℝ 2 (r26t3_mu R 0)) =
        (he j).1.toLp (e j)) ∧
      ∀ v : s21h2_V (r26t3_mu R 0),
        Tendsto (fun n => ∫ ω,
          (I.η (fun x => (((v - ∑ j ∈ Finset.range n,
            inner ℝ (b j) v • b j : s21h2_V (r26t3_mu R 0)) :
              Lp ℝ 2 (r26t3_mu R 0)) x)) ω)^2
              ∂(r26t3_tilt I.P (fun ω => γ * Q ω)))
          atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  letI := I.mΩ
  letI := I.prob
  obtain ⟨lam, e, he, hon, hsum, hKernel, hfull⟩ :=
    r26t3_kernel_spectral hδ hδh R
  have hStd : HRS.IsStdGaussianSeq I.P (fun j => I.η (e j)) :=
    s15d_physical_spectral_standard_gaussian_seq I e
      (fun j => (he j).2) hon
  obtain ⟨Q, hQ, hExp1, _hZ, hLaw⟩ :=
    r26t3_hs_gaussian_tilt I.P (fun j => I.η (e j))
      hStd lam (fun j => (he j).1) hsum γ hγ
  obtain ⟨Q2, hQ2, _hExp1twice, hExp2Q2⟩ :=
    s15d_actual_tilt_square_integrable I.P (fun j => I.η (e j))
      hStd lam (fun j => (he j).1) hsum γ hγ
  have hQeq : Q =ᵐ[I.P] Q2 := by
    have hm : ∀ n, AEStronglyMeasurable
        (s21h2_s15c_Qn (fun j => I.η (e j)) lam n) I.P :=
      fun n => (s21h2_s15c_aemeas_Qn hStd lam n).aestronglyMeasurable
    exact HRS.TendstoL2.ae_unique hm hQ hQ2
  have hExp2 : Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) I.P := by
    apply hExp2Q2.congr
    filter_upwards [hQeq.symm] with ω hw
    simp only [hw]
  obtain ⟨b, hb⟩ := s15d_complete_physical_family_hilbert_basis
    e (fun j => (he j).2) hon hfull
  have hW : AEMeasurable (fun ω => γ * Q ω) I.P :=
    (hQ.1.const_mul γ).aemeasurable
  have hExp1' : Integrable
      (fun ω => Real.exp (-(γ * Q ω))) I.P := by
    simpa only [neg_mul] using hExp1
  have hExp2' : Integrable
      (fun ω => Real.exp (-(2 * (γ * Q ω)))) I.P := by
    convert hExp2 using 1
    funext ω
    ring
  refine ⟨lam, e, Q, (fun j => (he j).2), b,
    (fun j => (he j).1), hon, hsum, hKernel, hQ,
    hExp1, hExp2, hLaw, hb, ?_⟩
  intro v
  exact s15d_hilbert_basis_physical_tilt_tail I b v
    (fun ω => γ * Q ω) hW hExp1' hExp2'

#print axioms s15d_physical_riesz_alltest_spectral_tilt_projection
end HRS.MS.R26T3
