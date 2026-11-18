import HRS.Main.GFB1Aux2
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# I11: measurable continuous-path modification on a compact time interval.
# This is a general form of the measurable-modification argument, retaining
# a single full-measure set on which all times agree.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.GF

theorem r26t6c_measurable_continuous_modification
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Omega) (T : ℝ) (hT : 0 < T)
    (Z : ℝ → Omega → E)
    (hc : ∀ᵐ w ∂P, ContinuousOn (fun t => Z t w) (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P) :
    ∃ L : Omega → C(Set.Icc (0 : ℝ) T, E),
      Measurable L ∧
      ∀ᵐ w ∂P, ∀ t : Set.Icc (0 : ℝ) T, L w t = Z (t : ℝ) w := by
  classical
  obtain ⟨Z', hZm, hZc, hZa⟩ :=
    gf_measurable_modification_proof P T Z hc hm
  let L : Omega → C(Set.Icc (0 : ℝ) T, E) :=
    fun w => ⟨fun t => Z' (t : ℝ) w, (hZc w).restrict⟩
  have hLm : Measurable L := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hZm (t : ℝ)
  obtain ⟨s, hsc, hsd⟩ :
      ∃ s : Set (Set.Icc (0 : ℝ) T), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense _
  have hae : ∀ᵐ w ∂P, ∀ t ∈ s,
      Z' (t : ℝ) w = Z (t : ℝ) w := by
    exact (ae_ball_iff hsc).2 fun t ht => hZa (t : ℝ) t.2
  refine ⟨L, hLm, ?_⟩
  filter_upwards [hae, hc] with w hAw hCw
  have hE : (fun t : Set.Icc (0 : ℝ) T => Z' (t : ℝ) w) =
      (fun t : Set.Icc (0 : ℝ) T => Z (t : ℝ) w) := by
    exact Continuous.ext_on hsd (hZc w).restrict hCw.restrict
      (fun t ht => hAw t ht)
  intro t
  exact congrFun hE t

end HRS.MS.R26T6C
