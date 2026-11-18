import HRS.MC.CepP3Aux12

/-!
# Packet P3, Aux13: the parabolic Weyl lemma on the covering space `ℝ × (Fin N → Euc d)`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

theorem isAddHaar_volume_cov :
    (volume : Measure (ℝ × (Fin N → Euc d))).IsAddHaarMeasure := by
  have h1 : (volume : Measure (Fin N → Euc d)).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure ℝ).IsAddHaarMeasure := inferInstance
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure (Fin N → Euc d))

theorem isAddHaar_volume_euc :
    (volume : Measure (ℝ × EuclideanSpace ℝ (Fin (N * d)))).IsAddHaarMeasure := by
  have h1 : (volume : Measure (EuclideanSpace ℝ (Fin (N * d)))).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure ℝ).IsAddHaarMeasure := inferInstance
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ)
    (volume : Measure (EuclideanSpace ℝ (Fin (N * d))))

/-- The image of Lebesgue measure under `Acl` is a positive real multiple of Lebesgue measure. -/
theorem map_Acl_volume :
    ∃ c : ℝ, 0 < c ∧ Measure.map (Acl d N) (volume : Measure (ℝ × EuclideanSpace ℝ (Fin (N * d))))
      = ENNReal.ofReal c • (volume : Measure (ℝ × (Fin N → Euc d))) := by
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  haveI := isAddHaar_volume_euc (d := d) (N := N)
  haveI : (Measure.map (Acl d N) (volume : Measure (ℝ × EuclideanSpace ℝ (Fin (N * d))))).IsAddHaarMeasure :=
    (Acl d N).isAddHaarMeasure_map _
  set μ' := Measure.map (Acl d N) (volume : Measure (ℝ × EuclideanSpace ℝ (Fin (N * d)))) with hμ'
  have h := Measure.isAddLeftInvariant_eq_smul μ' (volume : Measure (ℝ × (Fin N → Euc d)))
  refine ⟨(μ'.addHaarScalarFactor volume : ℝ), ?_, ?_⟩
  · have hne : μ'.addHaarScalarFactor volume ≠ 0 := by
      intro h0
      have h00 : μ' = 0 := by rw [h, h0]; simp
      have hpos := Measure.IsOpenPosMeasure.open_pos (μ := μ') univ isOpen_univ univ_nonempty
      rw [h00] at hpos
      simp at hpos
    exact_mod_cast pos_iff_ne_zero.2 hne
  · refine h.trans ?_
    rw [ENNReal.ofReal_coe_nnreal]
    rfl

end HRS.MC.CepP3
