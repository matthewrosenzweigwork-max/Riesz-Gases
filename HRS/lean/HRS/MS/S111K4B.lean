import HRS.MS.S111K4A

/-!
# S11.1 / T01 (S11K4), part B: a centered Gaussian vector is a linear image of a standard Gaussian vector
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace HRS.MS.S111K4

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The law of a centered Gaussian vector `X : Ω → (ι → ℝ)` is `(k4gm ι).map (R *ᵥ ·)` for a matrix `R`. -/
theorem k4_rep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ι → ℝ) (hX : AEMeasurable X P) (hG : HRS.IsCenteredGaussian (P.map X)) :
    ∃ R : Matrix ι ι ℝ, P.map X = (k4gm ι).map (fun g => R.mulVec g) := by
  classical
  have : IsProbabilityMeasure (P.map X) :=
    ⟨by rw [Measure.map_apply_of_aemeasurable hX MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  have hGa : IsGaussian (P.map X) := hG.1
  set e : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm.toContinuousLinearMap with he
  have heX : ∀ ω, e (X ω) = WithLp.toLp 2 (X ω) := fun ω => rfl
  have hmemX : ∀ i, MemLp (fun ω => X ω i) 2 P := by
    intro i
    have h := IsGaussian.memLp_dual (P.map X) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i) 2 (by simp)
    exact (memLp_map_measure_iff (by fun_prop) hX).1 h
  have hmean : ∀ i, ∫ ω, X ω i ∂P = 0 := by
    intro i
    have h := hG.2 (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i)
    rw [integral_map hX (by fun_prop)] at h
    simpa using h
  set Cm : Matrix ι ι ℝ := Matrix.of fun i j => ∫ ω, X ω i * X ω j ∂P with hCm
  have hint : ∀ i j, Integrable (fun ω => X ω i * X ω j) P := fun i j => (hmemX i).integrable_mul (hmemX j)
  have hpsd : Cm.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · ext i j
      simp [hCm, Matrix.conjTranspose_apply, mul_comm]
    · intro x
      have : star x ⬝ᵥ Cm.mulVec x = ∫ ω, (∑ i, x i * X ω i) ^ 2 ∂P := by
        have e1 : ∀ ω, (∑ i, x i * X ω i) ^ 2 = ∑ i, ∑ j, (x i * x j) * (X ω i * X ω j) := fun ω => by
          rw [sq, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
        simp_rw [e1]
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
        simp only [dotProduct, Matrix.mulVec, hCm, Matrix.of_apply, Finset.mul_sum, star_trivial]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]; ring
      rw [this]
      exact integral_nonneg fun ω => sq_nonneg _
  -- the Euclidean image is Gaussian
  set γ' : Measure (EuclideanSpace ℝ ι) := (P.map X).map e with hγ'
  have : IsGaussian γ' := by rw [hγ']; infer_instance
  have hγ'eq : γ' = P.map (fun ω => WithLp.toLp 2 (X ω)) := by
    rw [hγ']
    exact e.continuous.measurable.aemeasurable.map_map_of_aemeasurable hX
  have hcov : covarianceBilin γ' = covarianceBilin (multivariateGaussian (0 : EuclideanSpace ℝ ι) Cm) := by
    ext x y
    rw [covarianceBilin_multivariateGaussian hpsd, hγ'eq]
    have := covarianceBilin_apply_pi (μ := P) (X := fun i ω => X ω i) hmemX x y
    refine this.trans ?_
    simp only [dotProduct, Matrix.mulVec, hCm, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [covariance, hmean]
    ring
  have hmean' : γ'[id] = (multivariateGaussian (0 : EuclideanSpace ℝ ι) Cm)[id] := by
    rw [integral_id_multivariateGaussian', hγ']
    show ∫ x, id x ∂((P.map X).map e) = 0
    rw [integral_map e.continuous.measurable.aemeasurable aestronglyMeasurable_id]
    have h0 : ∫ y, y ∂(P.map X) = 0 := by simpa using HRS.gaussian_integral_id_eq_zero hG
    have h1 : ∫ x, id (e x) ∂(P.map X) = e (∫ x, x ∂(P.map X)) := e.integral_comp_id_comm IsGaussian.integrable_id
    rw [h1, h0]
    simp
  have hEq : γ' = multivariateGaussian (0 : EuclideanSpace ℝ ι) Cm := IsGaussian.ext hmean' hcov
  refine ⟨CFC.sqrt Cm, ?_⟩
  have h1 : P.map X = γ'.map (fun x : EuclideanSpace ℝ ι => WithLp.ofLp x) := by
    rw [hγ', Measure.map_map (by fun_prop) e.continuous.measurable]
    have : (fun x : EuclideanSpace ℝ ι => WithLp.ofLp x) ∘ e = id := by
      ext x i; rfl
    rw [this, Measure.map_id]
  rw [h1, hEq, multivariateGaussian, ← map_pi_eq_stdGaussian (ι := ι)]
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext g i
  simp [Matrix.toEuclideanCLM_toLp]

end HRS.MS.S111K4
