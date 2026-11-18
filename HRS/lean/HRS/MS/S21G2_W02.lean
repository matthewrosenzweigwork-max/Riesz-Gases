import HRS.MS.S21G2_W00

/-!
# S21G2 W02 -- Hilbert, completeness and measurable structures of the weighted field space (R26-T3.W02)

`TestE` is a closed subspace of the separable Hilbert space `JetSpace`; `FieldF = StrongDual TestE` is identified with `TestE` by the Riesz
isometry (inner product, second countability); the Borel structure is chosen once.  Contract verbatim; helper names carry `s21g2_w02_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

instance s21g2_w02_jet_complete (d r : ℕ) (P : ℝ) : CompleteSpace (JetSpace d r P) := by
  unfold JetSpace; infer_instance

instance r26t3_test_complete (d r : ℕ) (P : ℝ) : CompleteSpace (TestE d r P) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The Riesz identification gives an inner product on the strong dual of a real Hilbert space. -/
@[reducible] def s21g2_w02_dualInner (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    InnerProductSpace ℝ (StrongDual ℝ E) where
  inner x y := inner ℝ ((InnerProductSpace.toDual ℝ E).symm x) ((InnerProductSpace.toDual ℝ E).symm y)
  norm_sq_eq_re_inner x := by
    have h := real_inner_self_eq_norm_sq ((InnerProductSpace.toDual ℝ E).symm x)
    rw [LinearIsometryEquiv.norm_map] at h
    simpa using h.symm
  conj_inner_symm x y := by
    simpa using real_inner_comm ((InnerProductSpace.toDual ℝ E).symm x) ((InnerProductSpace.toDual ℝ E).symm y)
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y c := by simp [real_inner_smul_left]

instance r26t3_field_inner (d r : ℕ) (P : ℝ) : InnerProductSpace ℝ (FieldF d r P) :=
  s21g2_w02_dualInner (TestE d r P)

instance s21g2_w02_wm_sfinite (d : ℕ) (P : ℝ) : SFinite (r26t3_weightMeasure d P) := by
  unfold r26t3_weightMeasure; infer_instance

instance s21g2_w02_jet_sc (d r : ℕ) (P : ℝ) : SecondCountableTopology (JetSpace d r P) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  unfold JetSpace; infer_instance

instance r26t3_field_secondCountable (d r : ℕ) (P : ℝ) : SecondCountableTopology (FieldF d r P) := by
  haveI : SecondCountableTopology (TestE d r P) := inferInstance
  exact ((InnerProductSpace.toDual ℝ (TestE d r P)).symm.toHomeomorph.isInducing).secondCountableTopology

instance r26t3_field_measurable (d r : ℕ) (P : ℝ) : MeasurableSpace (FieldF d r P) := borel _
instance r26t3_field_borel (d r : ℕ) (P : ℝ) : BorelSpace (FieldF d r P) := ⟨rfl⟩

end HRS.MS.R26T3
