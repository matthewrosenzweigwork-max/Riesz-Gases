import HRS.Sections.IIDAux10

/-!
# IID helper chain, part 11: coupling of two Gram Gaussians (finite-dimensional white-noise coupling).

For `u v : Fin p → H` in a real inner product space there is a coupling of
`N(0, Gram u)` and `N(0, Gram v)` with `E‖X - Y‖² = ∑ ‖u_a - v_a‖²`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Gram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The map `x ↦ (⟨w_a, x⟩)_a`. -/
def Aw {p : ℕ} (w : Fin p → V) : V →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  ∑ a : Fin p, (innerSL ℝ (w a)).smulRight (EuclideanSpace.single a (1 : ℝ))

lemma Aw_apply {p : ℕ} (w : Fin p → V) (x : V) (a : Fin p) : Aw w x a = inner ℝ (w a) x := by
  simp [Aw, Pi.single_apply]

lemma Aw_adjoint {p : ℕ} (w : Fin p → V) (u : EuclideanSpace ℝ (Fin p)) :
    (Aw w).adjoint u = ∑ a, u a • w a := by
  refine ext_inner_right ℝ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner]
  simp only [inner_smul_left, Aw_apply, PiLp.inner_apply]
  simp [mul_comm]

lemma law_Aw {p : ℕ} (w : Fin p → V) :
    (stdGaussian V).map (Aw w) = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p))
      (Matrix.gram ℝ w) := by
  have hGA : IsGaussian ((stdGaussian V).map (Aw w)) := inferInstance
  have hmA : ((stdGaussian V).map (Aw w))[id] = 0 := by
    show ∫ z, id z ∂((stdGaussian V).map (Aw w)) = 0
    rw [integral_map (Aw w).continuous.aemeasurable aestronglyMeasurable_id]
    simp only [id]
    rw [(Aw w).integral_comp_id_comm IsGaussian.integrable_id, integral_id_stdGaussian, map_zero]
  refine IsGaussian.ext (hmA.trans integral_id_multivariateGaussian'.symm) ?_
  ext u v
  rw [covarianceBilin_multivariateGaussian (Matrix.posSemidef_gram ℝ w),
    covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian]
  show inner ℝ ((Aw w).adjoint u) ((Aw w).adjoint v) = _
  rw [Aw_adjoint, Aw_adjoint, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, dotProduct, Matrix.mulVec,
    Matrix.gram_apply, Finset.mul_sum, RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


lemma integral_inner_sq_std (w : V) : ∫ x, (inner ℝ w x) ^ 2 ∂(stdGaussian V) = ‖w‖ ^ 2 := by
  have h := variance_dual_stdGaussian (E := V) (innerSL ℝ w)
  rw [variance_of_integral_eq_zero (innerSL ℝ w).continuous.aemeasurable
    (integral_strongDual_stdGaussian _)] at h
  simpa [innerSL_apply_norm] using h

end Gram

section Coupling

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma gram_coupling {p : ℕ} (u v : Fin p → H) :
    ∃ P : Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)), IsProbabilityMeasure P ∧
      P.map Prod.fst = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.gram ℝ u) ∧
      P.map Prod.snd = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (Matrix.gram ℝ v) ∧
      Integrable (fun z => ‖z.1 - z.2‖ ^ 2) P ∧
      ∫ z, ‖z.1 - z.2‖ ^ 2 ∂P = ∑ a, ‖u a - v a‖ ^ 2 := by
  classical
  set S : Set H := Set.range u ∪ Set.range v with hS
  have hSf : S.Finite := (Set.finite_range u).union (Set.finite_range v)
  let V : Submodule ℝ H := Submodule.span ℝ S
  haveI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ hSf
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  let u' : Fin p → V := fun a => ⟨u a, Submodule.subset_span (Or.inl ⟨a, rfl⟩)⟩
  let v' : Fin p → V := fun a => ⟨v a, Submodule.subset_span (Or.inr ⟨a, rfl⟩)⟩
  have hgu : Matrix.gram ℝ u' = Matrix.gram ℝ u := by
    ext a b; simp [Matrix.gram_apply, u']
  have hgv : Matrix.gram ℝ v' = Matrix.gram ℝ v := by
    ext a b; simp [Matrix.gram_apply, v']
  have hJ : Measurable fun x : V => (Aw u' x, Aw v' x) :=
    (Aw u').continuous.measurable.prodMk (Aw v').continuous.measurable
  refine ⟨(stdGaussian V).map fun x => (Aw u' x, Aw v' x), ⟨by
      rw [Measure.map_apply hJ MeasurableSet.univ]; simp⟩, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hJ]
    exact (law_Aw u').trans (by rw [hgu])
  · rw [Measure.map_map measurable_snd hJ]
    exact (law_Aw v').trans (by rw [hgv])
  · have hm : Measurable fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) => ‖z.1 - z.2‖ ^ 2 :=
      (measurable_fst.sub measurable_snd).norm.pow_const 2
    have e : ∀ x : V, ‖Aw u' x - Aw v' x‖ ^ 2 = ∑ a, (inner ℝ (u' a - v' a) x) ^ 2 := by
      intro x
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [Aw_apply, inner_sub_left]
    have hint : ∀ a, Integrable (fun x : V => (inner ℝ (u' a - v' a) x) ^ 2) (stdGaussian V) := by
      intro a
      have := (IsGaussian.memLp_dual (stdGaussian V) (innerSL ℝ (u' a - v' a)) 2 (by simp))
      exact this.integrable_sq
    have hint2 : Integrable (fun x : V => ‖Aw u' x - Aw v' x‖ ^ 2) (stdGaussian V) := by
      simp_rw [e]; exact integrable_finset_sum _ fun a _ => hint a
    refine ⟨(integrable_map_measure hm.aestronglyMeasurable hJ.aemeasurable).2 hint2, ?_⟩
    rw [integral_map hJ.aemeasurable hm.aestronglyMeasurable]
    simp_rw [e]
    rw [integral_finsetSum _ fun a _ => hint a]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_inner_sq_std]
    rfl

end Coupling

end HRS.IID
