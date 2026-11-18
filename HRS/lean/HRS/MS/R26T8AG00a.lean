import HRS.MS.R26T8AD00

/-!
# S8.2 observed-time layer, packet T8A.G00 (helper a): the Euclidean collision set is Lebesgue-null

`eucCollisionSet d N = ⋃_{i ≠ j} {X | X i = X j}`; each set is the kernel of the linear map `X ↦ X i - X j`,
which is a proper submodule when `d ≥ 1`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_g00_coll_null (d N : ℕ) (hd : 1 ≤ d) :
    volume (eucCollisionSet d N) = 0 := by
  have hset : eucCollisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j),
      (LinearMap.ker (((LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i) - (LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j) : (Fin N → Euc d) →ₗ[ℝ] Euc d)) :
        Set (Fin N → Euc d)) := by
    ext X
    simp only [eucCollisionSet, mem_setOf_eq, mem_iUnion, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero]
    constructor
    · rintro ⟨i, j, hij, h⟩
      exact ⟨i, j, hij, h⟩
    · rintro ⟨i, j, hij, h⟩
      exact ⟨i, j, hij, h⟩
  rw [hset]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => measure_iUnion_null fun hij => ?_
  apply Measure.addHaar_submodule
  intro htop
  have hmem : (Pi.single i (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)) : Fin N → Euc d) ∈
      LinearMap.ker (((LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i) - (LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j) : (Fin N → Euc d) →ₗ[ℝ] Euc d)) := by
    rw [htop]
    trivial
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply, LinearMap.proj_apply,
    Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij), sub_eq_zero] at hmem
  have hne : (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Euc d) ≠ 0 := by
    intro h
    have := congrArg (fun v : Euc d => v ⟨0, hd⟩) h
    simp at this
  exact hne (by simpa using hmem)

end HRS.MS.R26T8A

end
