import HRS.Whole.SteinAux6

/-!
# Packet STEIN, auxiliary file 7: Hilbert-space coordinates and projections
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein

section HilbertBlocks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Same body as `HRS.Whole.hilbertCoords`. -/
def hcoords (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => inner ℝ (e i) x

/-- Same body as `HRS.Whole.hilbertProj`. -/
def hproj (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : H :=
  ∑ i ∈ Finset.range n, inner ℝ (e i) x • e i

lemma hilbert_secondCountable (e : HilbertBasis ℕ ℝ H) : SecondCountableTopology H := by
  have hsep : TopologicalSpace.IsSeparable (Set.range (e : ℕ → H)) :=
    (Set.countable_range _).isSeparable
  have h2 := hsep.span (R := ℝ)
  have hd : Dense ((Submodule.span ℝ (Set.range (e : ℕ → H)) : Submodule ℝ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact e.dense_span
  have h3 : TopologicalSpace.IsSeparable (Set.univ : Set H) := by
    have := h2.closure
    rwa [hd.closure_eq] at this
  have : TopologicalSpace.SeparableSpace H := TopologicalSpace.isSeparable_univ_iff.1 h3
  exact UniformSpace.secondCountable_of_separable H

/-- The coordinate map as a continuous linear map. -/
def coordCLM (e : HilbertBasis ℕ ℝ H) (n : ℕ) : H →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.mkContinuous
    { toFun := hcoords e n
      map_add' := by
        intro x y; ext i; simp [hcoords, inner_add_right]
      map_smul' := by
        intro c x; ext i; simp [hcoords, inner_smul_right] }
    1 (by
      intro x
      rw [one_mul, EuclideanSpace.norm_eq]
      have h := (e.orthonormal.comp (fun i : Fin n => (i : ℕ)) Fin.val_injective).sum_inner_products_le
        x (s := Finset.univ)
      refine Real.sqrt_le_left (norm_nonneg x) |>.2 ?_
      simpa [hcoords] using h)

lemma coordCLM_apply (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : coordCLM e n x = hcoords e n x := rfl

/-- The embedding of `ℝⁿ` onto the span of the first `n` basis vectors. -/
def embCLM (e : HilbertBasis ℕ ℝ H) (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] H :=
  ∑ i : Fin n, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).smulRight (e i)

lemma embCLM_apply (e : HilbertBasis ℕ ℝ H) (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    embCLM e n y = ∑ i : Fin n, y i • e i := by
  simp [embCLM]

lemma norm_embCLM_apply (e : HilbertBasis ℕ ℝ H) (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖embCLM e n y‖ = ‖y‖ := by
  rw [embCLM_apply]
  have horth : Orthonormal ℝ (fun i : Fin n => e (i : ℕ)) :=
    e.orthonormal.comp (fun i : Fin n => (i : ℕ)) Fin.val_injective
  have h := horth.inner_sum (fun i => y i) (fun i => y i) Finset.univ
  have h2 : ‖∑ i : Fin n, y i • e (i : ℕ)‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, h, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs, sq_abs, sq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

lemma norm_embCLM_le (e : HilbertBasis ℕ ℝ H) (n : ℕ) : ‖embCLM e n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [norm_embCLM_apply, one_mul]

lemma norm_coordCLM_le (e : HilbertBasis ℕ ℝ H) (n : ℕ) : ‖coordCLM e n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma embCLM_coords (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) :
    embCLM e n (hcoords e n x) = hproj e n x := by
  rw [embCLM_apply]
  unfold hproj hcoords
  exact Fin.sum_univ_eq_sum_range (fun i => inner ℝ (e i) x • e i) n

lemma hproj_eq_comp (e : HilbertBasis ℕ ℝ H) (n : ℕ) :
    hproj e n = fun x => embCLM e n (coordCLM e n x) := by
  funext x; rw [coordCLM_apply, embCLM_coords]

lemma hproj_continuous (e : HilbertBasis ℕ ℝ H) (n : ℕ) : Continuous (hproj e n) := by
  rw [hproj_eq_comp]; exact (embCLM e n).continuous.comp (coordCLM e n).continuous

lemma norm_hproj_le (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : ‖hproj e n x‖ ≤ ‖x‖ := by
  rw [hproj_eq_comp, norm_embCLM_apply]
  calc ‖coordCLM e n x‖ ≤ ‖coordCLM e n‖ * ‖x‖ := (coordCLM e n).le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (norm_coordCLM_le e n) (norm_nonneg _)
    _ = ‖x‖ := one_mul _

end HilbertBlocks

end HRS.Whole.Stein
