import HRS.MP.SelfSimP5DsEquiv

/-!
# P5 dissipation on `Fin N`: transport of the entropy
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Ds

/-- The measurable equivalence underlying `p5d_e`. -/
def p5d_em (N : ℕ) : EuclideanSpace ℝ (Fin N) ≃ᵐ EucConfig 1 N :=
  (p5d_e N).toHomeomorph.toMeasurableEquiv

theorem p5d_em_coe (N : ℕ) : (p5d_em N : EuclideanSpace ℝ (Fin N) → EucConfig 1 N) = p5d_e N := rfl

theorem p5d_measurableEmbedding (N : ℕ) : MeasurableEmbedding (p5d_e N) := by
  have := (p5d_em N).measurableEmbedding
  rwa [p5d_em_coe] at this

theorem p5d_measurable (N : ℕ) : Measurable (p5d_e N) := (p5d_measurableEmbedding N).measurable

/-- The transported potential. -/
def p5d_V {N : ℕ} (U : EuclideanSpace ℝ (Fin N) → ℝ) : EucConfig 1 N → ℝ :=
  fun x => U ((p5d_e N).symm x)

theorem p5d_klDiv_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν e.measurable) ?_
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  rw [Measure.map_map e.symm.measurable e.measurable, Measure.map_map e.symm.measurable e.measurable] at h
  have e1 : ((e.symm : β → α) ∘ (e : α → β)) = id := by funext x; simp
  rw [e1, Measure.map_id, Measure.map_id] at h
  exact h

theorem p5d_partition {N : ℕ} (θ : ℝ) (U : EuclideanSpace ℝ (Fin N) → ℝ) :
    gibbsPartitionW (p4GibbsOf θ (p5d_V U)) = ss5_partition θ U := by
  unfold gibbsPartitionW ss5_partition
  rw [← (p5d_measurePreserving N).lintegral_comp_emb (p5d_measurableEmbedding N)]
  refine lintegral_congr fun z => ?_
  simp [p4GibbsOf, p5d_V, div_eq_inv_mul]

theorem p5d_ref {N : ℕ} (θ : ℝ) (U : EuclideanSpace ℝ (Fin N) → ℝ) :
    gibbsRefW (p4GibbsOf θ (p5d_V U)) = (ss5_ref θ U).map (p5d_e N) := by
  have hm := p5d_measurableEmbedding N
  ext s hs
  unfold gibbsRefW ss5_ref
  rw [p5d_partition, Measure.map_apply hm.measurable hs]
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [withDensity_apply _ hs, withDensity_apply _ (hm.measurable hs)]
  rw [← (p5d_measurePreserving N).setLIntegral_comp_preimage_emb hm]
  refine lintegral_congr fun z => ?_
  simp [p4GibbsOf, p5d_V, div_eq_inv_mul]

instance p5d_ref_finite {N : ℕ} (θ : ℝ) (U : EuclideanSpace ℝ (Fin N) → ℝ) :
    IsFiniteMeasure (ss5_ref θ U) := by
  refine ⟨?_⟩
  unfold ss5_ref
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  have : ∫⁻ z, ENNReal.ofReal (Real.exp (-U z / θ)) = ss5_partition θ U := rfl
  rw [this]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one (ss5_partition θ U)) ENNReal.one_lt_top

theorem p5d_ent {N : ℕ} (θ : ℝ) (U : EuclideanSpace ℝ (Fin N) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin N))) [IsFiniteMeasure μ] :
    ss5_ent θ U μ = gibbsEntropyW (p4GibbsOf θ (p5d_V U)) (μ.map (p5d_e N)) := by
  unfold ss5_ent gibbsEntropyW relEntropy
  rw [p5d_ref, p5d_partition, ← p5d_em_coe, p5d_klDiv_equiv (p5d_em N) μ (ss5_ref θ U)]

end HRS.MP.SelfSimP5Ds
