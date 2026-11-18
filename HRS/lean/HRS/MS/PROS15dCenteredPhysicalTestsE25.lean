import HRS.MS.PROS15dSpatialProjectionE25
import HRS.MS.PROS15dPhysicalSpanE24
import HRS.MS.PROS15dTestGaussianBridgeC19

/-!
# S15d: Gaussianity of every centered physical spatial L² representative

A complete orthonormal physical spatial basis, finite Gaussian laws
under one fixed tilt, and the true Gaussian first-chaos continuity
suffice. Unlike a statement only about abstract L² classes, this
conclusion applies directly to each original physical test function.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3
open HRS.Whole.Q34

theorem s15d_hilbert_spectral_tilted_centered_test_gaussian
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ) (W : I.Ω → ℝ)
    (hW : AEMeasurable W I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-W ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * W ω))) I.P)
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ j, MemLp (e j) 2 μ)
    (b : HilbertBasis ℕ ℝ (s21h2_V μ))
    (hb : ∀ j, ((b j : s21h2_V μ) : Lp ℝ 2 μ) =
      (he j).toLp (e j))
    (hFinite : ∀ (n : ℕ) (a : Fin n → ℝ),
      HRS.IsCenteredGaussian
        ((r26t3_tilt I.P W).map
          (I.η (fun x => ∑ j : Fin n, a j * e j x))))
    (f : HRS.Euc d → ℝ)
    (hf : HRS.Whole.MemL2Zero μ f) :
    HRS.IsCenteredGaussian
      ((r26t3_tilt I.P W).map (I.η f)) := by
  classical
  letI := I.mΩ
  letI := I.prob
  let v : s21h2_V μ :=
    ⟨(hf.1).toLp f, by
      rw [s21h2_mem_V, inner_one2]
      rw [integral_congr_ae (hf.1.coeFn_toLp)]
      exact hf.2⟩
  let u : ℕ → HRS.Euc d → ℝ := fun n x =>
    ∑ j ∈ Finset.range n, inner ℝ (b j) v * e j x
  have hu : ∀ n, MemLp (u n) 2 μ := by
    intro n
    exact memLp_finsetSum _ (fun j _ => (he j).const_mul _)
  have hG : ∀ n, HRS.IsCenteredGaussian
      ((r26t3_tilt I.P W).map (I.η (u n))) := by
    intro n
    simpa only [u, Finset.sum_range] using
      hFinite n (fun j : Fin n => inner ℝ (b j) v)
  have hS : Tendsto (fun n =>
      ∫ x, (u n x - (((v : s21h2_V μ) : Lp ℝ 2 μ) x)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    simpa only [u] using
      s15d_physical_hilbert_spatial_projection_L2 e he b hb v
  have hRep :
      (fun x => (((v : s21h2_V μ) : Lp ℝ 2 μ) x)) =ᵐ[μ] f := by
    exact (hf.1.coeFn_toLp)
  have hSame (n : ℕ) :
      (∫ x, (u n x - f x) ^ 2 ∂μ) =
        ∫ x, (u n x - (((v : s21h2_V μ) : Lp ℝ 2 μ) x)) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hRep] with x hx
    rw [hx]
  have hSpatial :
      Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 ∂μ)
        atTop (𝓝 0) := by
    simpa only [hSame] using hS
  exact s15d_physical_tilted_gaussian_of_spatial_approximation
    I W hW hExp1 hExp2 f hf.1 u hu hG hSpatial

#print axioms s15d_hilbert_spectral_tilted_centered_test_gaussian
end HRS.MS.R26T3
