import HRS.MS.Fp81S21BV011
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Bases

/-! Closed image spaces and norm-preserving transports for anchored BV paths. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21
open TopologicalSpace

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : ℝ} (hH : 0 ≤ H) [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The closed linear image of a continuous linear map into the anchored BV path space. -/
def fp81s21_bvImage (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    Submodule ℝ (fp81s21_BV0 (E := E) hH) :=
  T.toLinearMap.range.topologicalClosure

/-- A closed subspace of a complete BV path space is complete. -/
instance fp81s21_bvImage_complete[CompleteSpace E] (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    CompleteSpace (fp81s21_bvImage hH T) :=
  (Submodule.isClosed_topologicalClosure T.toLinearMap.range).isComplete.completeSpace_coe

/-- If the source is separable, the closed image is separable. -/
instance fp81s21_bvImage_separable [SeparableSpace U]
    (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    SeparableSpace (fp81s21_bvImage hH T) := by
  apply IsSeparable.separableSpace
  change IsSeparable (closure (Set.range T))
  exact (isSeparable_range T.continuous).closure

/-- A separable BV image is second countable in its inherited norm topology. -/
theorem fp81s21_bvImage_secondCountable [SeparableSpace U]
    (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    SecondCountableTopology (fp81s21_bvImage hH T) := by
  infer_instance

/-- Equip each closed image with the Borel sigma-algebra of its norm topology. -/
noncomputable instance fp81s21_bvImage_measurableSpace
    (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    MeasurableSpace (fp81s21_bvImage hH T) :=
  borel _

/-- The image's measurable-space instance is exactly its Borel sigma-algebra. -/
instance fp81s21_bvImage_borelSpace
    (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    BorelSpace (fp81s21_bvImage hH T) := ⟨rfl⟩

/-- Corestrict the transport to its closed image. -/
def fp81s21_bvTransport (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) :
    U →L[ℝ] fp81s21_bvImage hH T :=
  T.codRestrict (fp81s21_bvImage hH T) (fun x =>
    T.toLinearMap.range.le_topologicalClosure ⟨x, rfl⟩)

/-- Coercing the transport back to the BV space recovers the original map. -/
theorem fp81s21_bvTransport_coe (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) (x : U) :
    ((fp81s21_bvTransport hH T x : fp81s21_bvImage hH T) :
      fp81s21_BV0 (E := E) hH) = T x := rfl

/-- The image transport preserves the variation norm of each output. -/
theorem fp81s21_bvTransport_norm_eq (T : U →L[ℝ] fp81s21_BV0 (E := E) hH) (x : U) :
    ‖fp81s21_bvTransport hH T x‖ = ‖T x‖ := rfl

/-- Differences of transported paths satisfy the operator-norm bound. -/
theorem fp81s21_bvTransport_difference (T : U →L[ℝ] fp81s21_BV0 (E := E) hH)
    (x y : U) :
    ‖fp81s21_bvTransport hH T x - fp81s21_bvTransport hH T y‖ ≤
      ‖T‖ * ‖x - y‖ := by
  calc
    ‖fp81s21_bvTransport hH T x - fp81s21_bvTransport hH T y‖ =
        ‖fp81s21_bvTransport hH T (x - y)‖ := by rw [map_sub]
    _ = ‖T (x - y)‖ := fp81s21_bvTransport_norm_eq hH T (x - y)
    _ ≤ ‖T‖ * ‖x - y‖ := T.le_opNorm (x - y)

#print axioms fp81s21_bvImage
#print axioms fp81s21_bvImage_complete
#print axioms fp81s21_bvImage_separable
#print axioms fp81s21_bvImage_secondCountable
#print axioms fp81s21_bvImage_measurableSpace
#print axioms fp81s21_bvImage_borelSpace
#print axioms fp81s21_bvTransport
#print axioms fp81s21_bvTransport_coe
#print axioms fp81s21_bvTransport_norm_eq
#print axioms fp81s21_bvTransport_difference

end HRS.Fp81.S21

end
