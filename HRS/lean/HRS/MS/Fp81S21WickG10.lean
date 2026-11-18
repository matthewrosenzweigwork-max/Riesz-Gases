import HRS.MS.Fp81S21WickG9

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

/-- Every finite family in a real Hilbert space has an orthonormal basis of
its span, and each member has its usual inner-product coordinate expansion. -/
theorem fp81s21_wickG_span_orthonormal_decomposition
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (f : Fin n → Lp ℝ 2 μ) :
    ∃ q : ℕ, ∃ e : Fin q → Lp ℝ 2 μ,
      ∃ M : Fin n → Fin q → ℝ,
        Orthonormal ℝ e ∧
        ∀ i, f i = ∑ a, M i a • e a := by
  classical
  let F : Submodule ℝ (Lp ℝ 2 μ) := Submodule.span ℝ (Set.range f)
  haveI : FiniteDimensional ℝ F :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let b : OrthonormalBasis (Fin (Module.finrank ℝ F)) ℝ F :=
    stdOrthonormalBasis ℝ F
  have hmem : ∀ i, f i ∈ F := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  let xi : Fin n → F := fun i => ⟨f i, hmem i⟩
  let e : Fin (Module.finrank ℝ F) → Lp ℝ 2 μ := fun a => (b a : F)
  let M : Fin n → Fin (Module.finrank ℝ F) → ℝ :=
    fun i a => inner ℝ (b a) (xi i)
  refine ⟨Module.finrank ℝ F, e, M, ?_, ?_⟩
  · exact b.orthonormal.comp_linearIsometry F.subtypeₗᵢ
  · intro i
    have hrepr := b.sum_repr' (xi i)
    have hrepr' := congrArg (fun z : F => (z : Lp ℝ 2 μ)) hrepr
    simpa [M, e, xi, Submodule.coe_sum, Submodule.coe_smul] using hrepr'.symm

#print axioms fp81s21_wickG_span_orthonormal_decomposition

end HRS.Fp81.S21

end
