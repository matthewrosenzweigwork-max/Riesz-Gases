import HRS.MC.S7PIDefs
import HRS.MC.S7PIS2Obs

/-!
# Packet piS3, part 1: `s7_PIS_obs_law` (the observation vector of `γ_u` is a finite Gaussian)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIS3

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

local instance S7PIS3_pathSC {m T : ℝ} : SecondCountableTopology (PathSpace d m T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, NegSobolev d m))

local instance S7PIS3_pathComplete {m T : ℝ} : CompleteSpace (PathSpace d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- Gaussian moments of a continuous linear map to `ℝ^q`: the coordinates are in `L²`. -/
theorem S7PIS3_coord_memLp {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] {γ : Measure B} [IsGaussian γ] {q : ℕ} (O : B →L[ℝ] EuclideanSpace ℝ (Fin q))
    (i : Fin q) : MemLp (fun w => O w i) 2 γ := by
  have := IsGaussian.memLp_dual γ ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).comp O) 2
    (by simp)
  exact this

theorem S7PIS3_coord_mul_integrable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] {γ : Measure B} [IsGaussian γ] {q : ℕ}
    (O : B →L[ℝ] EuclideanSpace ℝ (Fin q)) (i j : Fin q) :
    Integrable (fun w => O w i * O w j) γ :=
  (S7PIS3_coord_memLp O i).integrable_mul (S7PIS3_coord_memLp O j)

/-- A centred Gaussian measure pushed by a continuous linear map to `ℝ^q` is the multivariate
Gaussian with the Gram matrix of the coordinates. -/
theorem S7PIS3_map_eq {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B] {γ : Measure B} [IsGaussian γ] (hc : ∀ L : StrongDual ℝ B, ∫ z, L z ∂γ = 0)
    {q : ℕ} (O : B →L[ℝ] EuclideanSpace ℝ (Fin q)) (S : Matrix (Fin q) (Fin q) ℝ)
    (hS : ∀ i j, S i j = ∫ w, O w i * O w j ∂γ) :
    S.PosSemidef ∧ γ.map O = multivariateGaussian 0 S := by
  have hmean : (γ.map O)[id] = 0 := by
    rw [integral_map O.continuous.aemeasurable aestronglyMeasurable_id]
    ext i
    have h1 : Integrable (fun w => O w) γ := O.integrable_comp IsGaussian.integrable_id
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ) h1
    simpa using (this.symm.trans (hc ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).comp O)))
  have hcov : ∀ x y : EuclideanSpace ℝ (Fin q),
      covarianceBilin (γ.map O) x y = dotProduct x (S.mulVec y) := by
    intro x y
    rw [covarianceBilin_apply IsGaussian.memLp_two_id]
    rw [hmean]
    rw [integral_map O.continuous.aemeasurable]
    · simp only [sub_zero, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      have : ∀ w, (∑ i, O w i * x i) * (∑ j, O w j * y j) =
          ∑ i, ∑ j, x i * y j * (O w i * O w j) := by
        intro w
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      simp_rw [this]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        (S7PIS3_coord_mul_integrable O i j).const_mul _)]
      simp only [dotProduct, Matrix.mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ => (S7PIS3_coord_mul_integrable O i j).const_mul _),
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul, hS i j]
      ring
    · exact (Measurable.aestronglyMeasurable (by fun_prop))
  have hpsd : S.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, hS]
      simp_rw [mul_comm (O _ j)]
    · intro x
      have := covarianceBilin_self_nonneg (μ := γ.map O) (WithLp.toLp 2 x)
      rw [hcov] at this
      simpa using this
  refine ⟨hpsd, ?_⟩
  refine IsGaussian.ext ?_ ?_
  · rw [hmean]; simp
  · ext x y
    rw [hcov, covarianceBilin_multivariateGaussian hpsd]

theorem s7_PIS_obs_law_proof (R : Regime d) (m : ℝ) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∀ u ∈ Set.Icc (0 : ℝ) T, (obsCov R.D R.ρ t φ u).PosSemidef ∧
      (γ u).map (obsVec m T t φ) = multivariateGaussian 0 (obsCov R.D R.ρ t φ u) := by
  intro u hu
  obtain ⟨O, hO⟩ := HRS.MC.Sec7.S7PIS2.s7_PIS_obs_clm_proof m T t φ ht hφ
  have hOf : (obsVec m T t φ) = fun w => O w := funext fun w => (hO w).symm
  obtain ⟨⟨hG, hc⟩, hcov⟩ := hγ u hu
  haveI : IsGaussian (γ u) := hG
  rw [hOf]
  refine S7PIS3_map_eq hc O _ fun i j => ?_
  have := hcov (t i) (t j) (φ i) (φ j) (hφ i) (hφ j) (ht i) (ht j)
  simp only [hO]
  simpa [obsCov, obsVec] using this.symm

end HRS.MC.Sec7.S7PIS3

end
