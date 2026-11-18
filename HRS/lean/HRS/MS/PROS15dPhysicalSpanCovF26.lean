import HRS.MS.PROS15dFiniteScalarCovF26
import HRS.MS.S21T4ProdF
import HRS.MS.PROS15dPhysicalFirstChaos

/-!
# S15d: finite covariance for actual physical first-chaos evaluations

The spectral scalar covariance is transported from the finite Gaussian
coordinate sums to the original ProductGaussian field acting on the spatial
linear combinations. Both a.e. first-chaos identities are transferred from
the reference law to the same normalized exponential tilted law.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_finite_span_scalar_covariance
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (W : I.Ω → ℝ) (hW : AEMeasurable W I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-W ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * W ω))) I.P)
    (e : ℕ → HRS.Euc d → ℝ) (he : ∀ j, MemLp (e j) 2 μ)
    (n : ℕ) (v : Fin n → ℝ≥0)
    (hLaw : (r26t3_tilt I.P W).map
      (fun ω (j : Fin n) => I.η (e j) ω) =
      Measure.pi (fun j : Fin n => gaussianReal 0 (v j)))
    (a b : Fin n → ℝ) :
    (∫ ω,
        I.η (fun x => ∑ j : Fin n, a j * e j x) ω *
        I.η (fun x => ∑ j : Fin n, b j * e j x) ω
      ∂(r26t3_tilt I.P W)) =
    ∑ j : Fin n, a j * b j * (v j : ℝ) := by
  classical
  letI := I.mΩ
  letI := I.prob
  let Pt := r26t3_tilt I.P W
  letI : IsProbabilityMeasure Pt := r26t3_tilt_isProb I.P hW hExp1
  have hAC : Pt ≪ I.P := by
    unfold Pt r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous I.P _ hs]
  have hfinite (c : Fin n → ℝ) :
      I.η (fun x => ∑ j : Fin n, c j * e j x) =ᵐ[Pt]
        fun ω => ∑ j : Fin n, c j * I.η (e j) ω := by
    have hp : I.η (fun x => ∑ j : Fin n, c j * e j x) =ᵐ[I.P]
        fun ω => ∑ j : Fin n, c j * I.η (e j) ω := by
      simpa only [] using
        s21l_eta_sum (s21t4_product_eta_bundle I)
          Finset.univ c (fun j : Fin n => e j)
          (fun j _ => he j)
    exact hAC hp
  have hX : ∀ i : Fin n, MemLp (I.η (e i)) 2 Pt := by
    intro i
    exact s15d_physical_first_chaos_tilt_L2 I (e i) (he i)
      W hW hExp1 hExp2
  have hCov := s15d_finite_spectral_scalar_covariance
    (fun i : Fin n => I.η (e i)) hX v hLaw a b
  calc
    (∫ ω,
        I.η (fun x => ∑ j : Fin n, a j * e j x) ω *
        I.η (fun x => ∑ j : Fin n, b j * e j x) ω ∂Pt) =
      ∫ ω,
        (∑ j : Fin n, a j * I.η (e j) ω) *
        (∑ j : Fin n, b j * I.η (e j) ω) ∂Pt := by
          refine integral_congr_ae ?_
          filter_upwards [hfinite a, hfinite b] with ω ha hb
          rw [ha, hb]
    _ = _ := hCov

#print axioms s15d_physical_finite_span_scalar_covariance
end HRS.MS.R26T3
