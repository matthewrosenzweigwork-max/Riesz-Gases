import HRS.MS.R26T8AA01t

/-!
# S8.2 T8A A01 (part u): decomposition of `pairJ` for a symmetric kernel
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_a01_pairJ_decomp (C : WholeCoeff d) (μ : Measure (Euc d)) {Q : Euc d → Euc d → ℝ}
    (hsymm : ∀ x y, Q x y = Q y x) (x y : Euc d) :
    pairJ C μ Q x y =
      (oneJ C (fun w => Q w y) x - ∫ t, oneJ C (fun u => Q u y) t ∂μ) +
      (oneJ C (fun w => Q w x) y - ∫ t, oneJ C (fun u => Q u x) t ∂μ) := by
  have e : Q x = fun w => Q w x := funext fun w => hsymm x w
  unfold pairJ HRS.Whole.projMean HRS.Whole.pair
  rw [e]

theorem r26t8a_a01_aesm_vec (hd : 2 ≤ d) (y : Euc d) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [SecondCountableTopology V] {φ : Euc d → V} (hφ : ContinuousOn φ {y}ᶜ) :
    AEStronglyMeasurable φ volume := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hs : MeasurableSet ({y}ᶜ : Set (Euc d)) := (measurableSet_singleton y).compl
  have h1 : AEStronglyMeasurable φ (volume.restrict {y}ᶜ) := hφ.aestronglyMeasurable hs
  have h2 : (volume : Measure (Euc d)).restrict {y}ᶜ = volume :=
    Measure.restrict_eq_self_of_ae_mem (compl_mem_ae_iff.mpr (measure_singleton y))
  rwa [h2] at h1

end HRS.MS.R26T8A
