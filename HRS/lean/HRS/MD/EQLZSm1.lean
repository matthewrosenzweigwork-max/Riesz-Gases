import HRS.Appendix.B15Final
import HRS.MD.EQLZVocab

/-!
# EQ-LZ packet SM, part 1: the initial density at a level (`dπ/dπ_k ≤ Z_k/Z`)

For the packet SM (`eqlz_smooth`): at level `M ≥ 0` the law of the true flow at time `0` (the canonical Gibbs law
`gibbsRef D N`, transported to `𝕋^{N d}`) has a bounded measurable density `ρ` with respect to the level Gibbs measure
`d1_gibbsMeasure D.invβ (b15d_U D M)`, with `0 ≤ ρ ≤ c`, `c = Z_M / Z` (`Z_M`, `Z` the partition functions).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

namespace MD

namespace EQLZSm

variable {d N : ℕ}

/-- A finite measure dominated by `c • π` has a bounded measurable density with respect to `π`. -/
theorem sm_exists_density {α : Type*} [MeasurableSpace α] (ν π : Measure α) [IsFiniteMeasure ν]
    [SigmaFinite π] (c : ℝ≥0∞) (hc : c ≠ ⊤) (h : ν ≤ c • π) :
    ∃ ρ : α → ℝ, Measurable ρ ∧ (∀ x, 0 ≤ ρ x ∧ ρ x ≤ c.toReal) ∧
      ν = π.withDensity (fun x => ENNReal.ofReal (ρ x)) := by
  have hle : ∀ s, ν s ≤ c * π s := fun s => by simpa using Measure.le_iff'.1 h s
  have hac : ν ≪ π := by
    intro s hs
    have := hle s
    rw [hs, mul_zero] at this
    exact nonpos_iff_eq_zero.1 this
  have hf : Measurable (ν.rnDeriv π) := Measure.measurable_rnDeriv ν π
  have hbd : ν.rnDeriv π ≤ᵐ[π] fun _ => c := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf fun s hs _ => ?_
    rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
    exact hle s
  refine ⟨fun x => min (ν.rnDeriv π x).toReal c.toReal, hf.ennreal_toReal.min measurable_const,
    fun x => ⟨le_min ENNReal.toReal_nonneg ENNReal.toReal_nonneg, min_le_right _ _⟩, ?_⟩
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν π hac]
  refine withDensity_congr_ae ?_
  filter_upwards [hbd] with x hx
  have hxt : ν.rnDeriv π x ≠ ⊤ := ne_top_of_le_ne_top hc hx
  rw [min_eq_left (ENNReal.toReal_mono hc hx), ENNReal.ofReal_toReal hxt]

/-- The level Gibbs measure dominates the true Gibbs law up to `Z_M / Z`. -/
theorem sm_gibbsRef_le (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {M : ℝ}
    (hM0 : 0 ≤ M) :
    gibbsRef D N ≤
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) * (gibbsPartition D N)⁻¹) •
        b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D M) := by
  obtain ⟨hZk_top, hZk_0⟩ := b15bp_partitionGen_bounds (N := N) D hβ hV hM0
  obtain ⟨hZg0, hZgt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  unfold gibbsRef b15c_gibbsRefGen
  rw [smul_smul]
  have hcancel : b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) *
      (gibbsPartition D N)⁻¹ * (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M))⁻¹ =
      (gibbsPartition D N)⁻¹ := by
    rw [mul_right_comm, ENNReal.mul_inv_cancel hZk_0 hZk_top, one_mul]
  rw [hcancel]
  refine Measure.le_iff'.2 fun s => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  gcongr
  exact withDensity_mono (μ := (volume : Measure (Config d N)))
    (Filter.Eventually.of_forall fun X => ENNReal.ofReal_le_ofReal (b15c_gibbsWeight_le_reg D hβ M X))

/-- The density of the (transported) true Gibbs law with respect to the level Gibbs measure on `𝕋^{N d}`:
`ρ` measurable, `0 ≤ ρ ≤ c` with `c = (Z_M / Z).toReal`. -/
theorem sm_level_density (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {M : ℝ}
    (hM0 : 0 ≤ M) [IsFiniteMeasure (gibbsRef D N)] :
    ∃ ρ : Torus (N * d) → ℝ, Measurable ρ ∧
      (∀ x, 0 ≤ ρ x ∧ ρ x ≤
        (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) *
          (gibbsPartition D N)⁻¹).toReal) ∧
      (gibbsRef D N).map (d1_configEquiv d N) =
        (d1_gibbsMeasure D.invβ (b15d_U (N := N) D M)).withDensity
          (fun x => ENNReal.ofReal (ρ x)) := by
  obtain ⟨hZk_top, hZk_0⟩ := b15bp_partitionGen_bounds (N := N) D hβ hV hM0
  obtain ⟨hZg0, hZgt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  have hcont := b15c_potentialReg_continuous (N := N) D (b15_continuous_of_isCk hV) M
  have : IsProbabilityMeasure (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D M)) :=
    b15c_gibbsRefGen_isProb _ _ hZk_top hZk_0
  have hmap := b15e_gibbsRefGen_map (N := N) D.invβ (b15c_potentialReg (N := N) D M)
  have hπ : d1_gibbsMeasure D.invβ (b15d_U (N := N) D M) =
      (b15c_gibbsRefGen D.invβ (b15c_potentialReg (N := N) D M)).map (d1_configEquiv d N) := hmap.symm
  have : IsProbabilityMeasure (d1_gibbsMeasure D.invβ (b15d_U (N := N) D M)) := by
    rw [hπ]; infer_instance
  have hc : (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) *
      (gibbsPartition D N)⁻¹) ≠ ⊤ := ENNReal.mul_ne_top hZk_top (ENNReal.inv_ne_top.mpr hZg0.ne')
  have hle : (gibbsRef D N).map (d1_configEquiv d N) ≤
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M) * (gibbsPartition D N)⁻¹) •
        d1_gibbsMeasure D.invβ (b15d_U (N := N) D M) := by
    rw [hπ]
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.map_apply (d1_configEquiv d N).measurable hs, Measure.smul_apply,
      Measure.map_apply (d1_configEquiv d N).measurable hs, smul_eq_mul]
    have := Measure.le_iff'.1 (sm_gibbsRef_le (N := N) D hβ hV hM0) ((d1_configEquiv d N) ⁻¹' s)
    simpa using this
  exact sm_exists_density _ _ _ hc hle

end EQLZSm

end MD

end HRS

end
