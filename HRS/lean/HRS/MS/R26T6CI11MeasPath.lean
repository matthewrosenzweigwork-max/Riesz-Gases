import HRS.MS.R26T6CI11Modify
import HRS.MS.R26T6CI11EvalMeas
import HRS.MS.R26T6CI11SamplePath

/-!
# I11: a measurable random continuous oscillator primitive from the
# genuine joint L³ derivative and measurable initial field.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole
variable {d : ℕ}

theorem r26t6c_measurable_oscillator_primitive
    (m T : ℝ) (hT : 0 < T)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (I : Omega → OscDual d m) (hI : MemLp I 3 P)
    (G : ℝ × Omega → OscDual d m)
    (hG : MemLp G 3 ((volume.restrict (Set.Icc 0 T)).prod P)) :
    ∃ L : Omega → OscPath d m T,
      AEMeasurable L P ∧
      ∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T,
        OscPath.at' (L w) t =
          I w + ∫ v in Set.Icc 0 (t : ℝ), G (v,w) := by
  let Z : ℝ → Omega → OscDual d m := fun t w =>
    I w + ∫ v in Set.Icc (0 : ℝ) t, G (v,w)
  have hc : ∀ᵐ w ∂P, ContinuousOn (fun t => Z t w) (Set.Icc 0 T) := by
    have hp := r26t6c_samplewise_continuous_primitive T hT P G hG
    filter_upwards [hp] with w hw
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => I w) (Set.Icc 0 T)).add hw
  have hm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P := by
    intro t ht
    exact hI.aestronglyMeasurable.aemeasurable.add
      (r26t6c_primitive_eval_aesm T P G
        hG.aestronglyMeasurable ⟨t,ht⟩).aemeasurable
  obtain ⟨L, hLm, hLae⟩ :=
    r26t6c_measurable_continuous_modification P T hT Z hc hm
  exact ⟨L, hLm.aemeasurable, hLae⟩

end HRS.MS.R26T6C
