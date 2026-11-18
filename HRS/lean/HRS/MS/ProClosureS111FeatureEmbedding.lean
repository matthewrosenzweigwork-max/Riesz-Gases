import HRS.Prob.HilbertCLT
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
A separable real Hilbert feature space embeds isometrically in one fixed
countable Gaussian-coordinate space. No infinite-dimensionality of the
physical feature space is required: a countable basis is injected into the
standard basis of ell²(N), with unused coordinates left zero.
-/
set_option autoImplicit false
noncomputable section
open Classical

namespace HRS.MS.ProClosureS111

abbrev GaussianFeatureHilbert := lp (fun _ : ℕ => ℝ) 2

def gaussianFeatureBasis : HilbertBasis ℕ ℝ GaussianFeatureHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ GaussianFeatureHilbert)

theorem separable_feature_embedding {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] :
    Nonempty (E →ₗᵢ[ℝ] GaussianFeatureHilbert) := by
  obtain ⟨ι, hcount, b, _⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type (H := E)
  letI : Countable ι := hcount
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat ι
  have hon : Orthonormal ℝ (fun i : ι => gaussianFeatureBasis (j i)) :=
    gaussianFeatureBasis.orthonormal.comp j hj
  exact ⟨hon.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry⟩

#print axioms separable_feature_embedding

end HRS.MS.ProClosureS111
