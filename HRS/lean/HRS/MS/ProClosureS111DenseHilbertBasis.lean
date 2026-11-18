import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Basic.Denumerable
import Mathlib.Topology.Bases
import Mathlib.Tactic.Linarith

/-!
A separable infinite-dimensional real Hilbert space has a countable
Hilbert basis contained in any given dense linear subspace. This is the
geometric step that allows the weighted chart's basis tests to remain
compactly supported and smooth, instead of choosing arbitrary completion
vectors as its tests.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Classical Set Topology
open scoped BigOperators

namespace HRS.MS.ProClosureS111

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SecondCountableTopology H]

/-- Gram--Schmidt on a dense sequence, discarding zero vectors, preserves
the prescribed dense linear subspace. Infinite dimensionality permits
indexing the resulting Hilbert basis by all natural numbers. -/
theorem hilbert_basis_in_dense_submodule (S : Submodule ℝ H)
    (hS : Dense (S : Set H)) (hinf : ¬ FiniteDimensional ℝ H) :
    ∃ b : HilbertBasis ℕ ℝ H, ∀ n, b n ∈ S := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq S
  let f : ℕ → H := fun n => u n
  have hval : DenseRange (fun y : S => (y : H)) := by
    change Dense (Set.range (fun y : S => (y : H)))
    have heq : Set.range (fun y : S => (y : H)) = (S : Set H) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [heq]
    exact hS
  have hf : DenseRange f := by
    refine Metric.denseRange_iff.2 fun x eps heps => ?_
    obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 hval x (eps / 2) (by linarith)
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hu y (eps / 2) (by linarith)
    refine ⟨n, ?_⟩
    have htri := dist_triangle x (y : H) (f n)
    change dist (y : H) (f n) < eps / 2 at hn
    linarith
  let g : ℕ → H := InnerProductSpace.gramSchmidtNormed ℝ f
  let I := {n : ℕ // g n ≠ 0}
  let v : I → H := fun i => g i
  have hv : Orthonormal ℝ v :=
    InnerProductSpace.gramSchmidtNormed_orthonormal' f
  have hspan0 : Submodule.span ℝ (range v) = Submodule.span ℝ (range g) := by
    apply le_antisymm
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨n, rfl⟩
      by_cases hn : g n = 0
      · rw [hn]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
  have hspan : Submodule.span ℝ (range v) = Submodule.span ℝ (range f) := by
    rw [hspan0]
    exact (InnerProductSpace.span_gramSchmidtNormed_range (𝕜 := ℝ) f).trans
      (InnerProductSpace.span_gramSchmidt ℝ f)
  have htop : ⊤ ≤ (Submodule.span ℝ (range v)).topologicalClosure := by
    rw [hspan]
    intro x _
    exact closure_mono (Submodule.subset_span : range f ⊆
      (Submodule.span ℝ (range f) : Set H)) (hf x)
  let bI : HilbertBasis I ℝ H := HilbertBasis.mk hv htop
  have hI : Infinite I := by
    constructor
    intro hfin
    letI : Finite I := hfin
    letI : Fintype I := Fintype.ofFinite I
    exact hinf bI.toOrthonormalBasis.toBasis.finiteDimensional_of_finite
  letI : Infinite I := hI
  let e : ℕ ≃ I := Classical.choice inferInstance
  have hve : Orthonormal ℝ (v ∘ e) := hv.comp e e.injective
  have hspanE : range (v ∘ e) = range v := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨e n, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp only [Function.comp_apply, Equiv.apply_symm_apply]⟩
  have htopE : ⊤ ≤ (Submodule.span ℝ (range (v ∘ e))).topologicalClosure := by
    rw [hspanE]
    exact htop
  refine ⟨HilbertBasis.mk hve htopE, fun n => ?_⟩
  rw [HilbertBasis.coe_mk]
  change g (e n) ∈ S
  unfold g InnerProductSpace.gramSchmidtNormed
  apply S.smul_mem
  have hmem := InnerProductSpace.gramSchmidt_mem_span ℝ f (le_refl (e n).val)
  apply (Submodule.span_le.2 ?_) hmem
  rintro _ ⟨j, _, rfl⟩
  exact (u j).property

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.hilbert_basis_in_dense_submodule

