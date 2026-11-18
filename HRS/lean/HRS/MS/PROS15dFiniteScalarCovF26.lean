import HRS.MS.PROS15dSpectralCovariance
import HRS.MS.S21G2_K11b

/-!
# S15d: finite spectral scalar covariance under the exact tilted Gaussian law

For possibly degenerate finite centered Gaussian spectral vectors, compute the
covariance of arbitrary two scalar linear combinations. This is the exact
finite-dimensional identity needed before Hilbert-basis completion. The
normalization and the spectral variances are not modified.
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_finite_spectral_scalar_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ}
    (X : Fin n → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P)
    (v : Fin n → ℝ≥0)
    (hLaw : P.map (fun ω (i : Fin n) => X i ω) =
      Measure.pi (fun i : Fin n => gaussianReal 0 (v i)))
    (a b : Fin n → ℝ) :
    (∫ ω, (∑ i : Fin n, a i * X i ω) *
      (∑ j : Fin n, b j * X j ω) ∂P) =
    ∑ i : Fin n, a i * b i * (v i : ℝ) := by
  classical
  have hXm : ∀ i, AEMeasurable (X i) P :=
    fun i => (hX i).aestronglyMeasurable.aemeasurable
  have hSumB : MemLp (fun ω => ∑ j : Fin n, b j * X j ω) 2 P :=
    memLp_finsetSum _ (fun j _ => (hX j).const_mul _)
  have hIntRow : ∀ i : Fin n,
      Integrable (fun ω => (a i * X i ω) *
        (∑ j : Fin n, b j * X j ω)) P :=
    fun i => ((hX i).const_mul _).integrable_mul hSumB
  calc
    (∫ ω, (∑ i : Fin n, a i * X i ω) *
      (∑ j : Fin n, b j * X j ω) ∂P) =
      ∑ i : Fin n, ∫ ω, (a i * X i ω) *
        (∑ j : Fin n, b j * X j ω) ∂P := by
          simp_rw [Finset.sum_mul]
          exact integral_finset_sum _ (fun i _ => hIntRow i)
    _ = ∑ i : Fin n, ∑ j : Fin n,
      (a i * b j) * (∫ ω, X i ω * X j ω ∂P) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp_rw [Finset.mul_sum]
          have hIntTerms : ∀ j : Fin n,
              Integrable (fun ω => (a i * X i ω) * (b j * X j ω)) P :=
            fun j => ((hX i).const_mul _).integrable_mul ((hX j).const_mul _)
          calc
            (∫ ω, ∑ j : Fin n, a i * X i ω * (b j * X j ω) ∂P) =
                ∑ j : Fin n, ∫ ω, a i * X i ω * (b j * X j ω) ∂P := by
                  exact integral_finset_sum _ (fun j _ => hIntTerms j)
            _ = _ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [← integral_const_mul]
              exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    _ = ∑ i : Fin n, ∑ j : Fin n,
        (if i = j then a i * b j * (v i : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => ?_)
          rw [s15d_pi_gaussian_covariance X hXm v hLaw i j]
          split_ifs <;> simp
    _ = ∑ i : Fin n, a i * b i * (v i : ℝ) := by simp

#print axioms s15d_finite_spectral_scalar_covariance
end HRS.MS.R26T3
