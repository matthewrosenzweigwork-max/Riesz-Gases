import HRS.MS.S111K4J01
import HRS.Energy.StaticLimitGauss

/-!
# S11.1 / J02, piece A (S111K4): measurability of the random L1 time coefficient

`k4j_timeCoeffOf_stronglyMeasurable`: for product-measurable `q`, the slice map `w ↦ timeCoeffOf H q w` into the separable
space `Lp Coeff 1` is strongly measurable (Pro J02, first clause).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

instance coeffSecondCountable : SecondCountableTopology Coeff :=
  have : TopologicalSpace.SeparableSpace Coeff := HRS.StaticLimitAux.separable_lp
  UniformSpace.secondCountable_of_separable Coeff

/-- A map into a separable metric space is measurable when all distance functions to points are. -/
theorem k4j_measurable_of_dist {Ω X : Type*} [MeasurableSpace Ω] [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {f : Ω → X} (h : ∀ g : X, Measurable fun w => dist (f w) g) :
    Measurable f := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  haveI : Countable D := hDc.to_subtype
  refine measurable_of_isOpen fun U hU => ?_
  have hU' : f ⁻¹' U = ⋃ (y : D) (n : ℕ) (_ : Metric.ball (y : X) (1 / ((n : ℝ) + 1)) ⊆ U),
      f ⁻¹' Metric.ball (y : X) (1 / ((n : ℝ) + 1)) := by
    ext w
    simp only [mem_preimage, mem_iUnion]
    constructor
    · intro hw
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hw
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨y, hyD, hy⟩ := hDd.exists_dist_lt (f w) (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
      refine ⟨⟨y, hyD⟩, n, ?_, ?_⟩
      · intro z hz
        apply hball
        rw [Metric.mem_ball] at hz ⊢
        have := dist_triangle z y (f w)
        rw [dist_comm y] at this
        linarith
      · rw [Metric.mem_ball]; exact hy
    · rintro ⟨y, n, hsub, hw⟩
      exact hsub hw
  rw [hU']
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => ?_
  have : f ⁻¹' Metric.ball (y : X) (1 / ((n : ℝ) + 1)) =
      (fun w => dist (f w) (y : X)) ⁻¹' Set.Iio (1 / ((n : ℝ) + 1)) := by
    ext w; simp [Metric.mem_ball]
  rw [this]
  exact (h _) measurableSet_Iio

end HRS.MS.S111K4J01
