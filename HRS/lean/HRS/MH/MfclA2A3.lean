import HRS.MH.MfclSpec

/-!
# Proofs of `HRS.MH.Mfcl.wassersteinE_one_real_ge_abs_mean_diff` (A2) and `HRS.MH.Mfcl.wassersteinE_one_ge_clm_mean_diff` (A3)

Statement-only packets from `HRS/MH/MfclSpec.lean`; proofs only, no statement is changed.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.MfclP

open HRS HRS.Main

/-- A2: on `ℝ`, `W₁` dominates the difference of the means (coupling argument, as `smoothDist_one_le_wasserstein`). -/
theorem wassersteinE_one_real_ge_abs_mean_diff_proof :
    type_of% @HRS.MH.Mfcl.wassersteinE_one_real_ge_abs_mean_diff := by
  intro μ ν _ _ hμ hν
  refine le_iInf fun π => ?_
  have : IsProbabilityMeasure π.1 := IsCoupling.isProbabilityMeasure π.2
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  have hi1 : Integrable (fun z : ℝ × ℝ => z.1) π.1 := by
    have h := hμ
    rw [← π.2.1] at h
    exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).1 h
  have hi2 : Integrable (fun z : ℝ × ℝ => z.2) π.1 := by
    have h := hν
    rw [← π.2.2] at h
    exact (integrable_map_measure aestronglyMeasurable_id measurable_snd.aemeasurable).1 h
  have e1 : ∫ x, x ∂μ = ∫ z, z.1 ∂π.1 := by
    have h := integral_map (μ := π.1) (φ := Prod.fst) (f := fun x : ℝ => x) measurable_fst.aemeasurable
      aestronglyMeasurable_id
    rwa [π.2.1] at h
  have e2 : ∫ x, x ∂ν = ∫ z, z.2 ∂π.1 := by
    have h := integral_map (μ := π.1) (φ := Prod.snd) (f := fun x : ℝ => x) measurable_snd.aemeasurable
      aestronglyMeasurable_id
    rwa [π.2.2] at h
  have hdiff : ∫ x, x ∂μ - ∫ x, x ∂ν = ∫ z, (z.1 - z.2) ∂π.1 := by
    rw [e1, e2, integral_sub hi1 hi2]
  rw [hdiff]
  calc ENNReal.ofReal |∫ z, (z.1 - z.2) ∂π.1|
      = ENNReal.ofReal ‖∫ z, (z.1 - z.2) ∂π.1‖ := by rw [Real.norm_eq_abs]
    _ ≤ ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ∂π.1) :=
          ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
    _ = ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 :=
          ofReal_integral_eq_lintegral_ofReal (hi1.sub hi2).norm (ae_of_all _ fun z => norm_nonneg _)

/-- A3: transfer of the mean-difference bound along a continuous linear functional. -/
theorem wassersteinE_one_ge_clm_mean_diff_proof :
    type_of% @HRS.MH.Mfcl.wassersteinE_one_ge_clm_mean_diff := by
  intro B _ _ _ _ ℓ P Q _ _ hP hQ
  have : IsProbabilityMeasure (P.map ℓ) :=
    (Measure.isProbabilityMeasure_map_iff ℓ.continuous.measurable.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (Q.map ℓ) :=
    (Measure.isProbabilityMeasure_map_iff ℓ.continuous.measurable.aemeasurable).2 inferInstance
  have hA2 := HRS.MH.MfclP.wassersteinE_one_real_ge_abs_mean_diff_proof (P.map ℓ) (Q.map ℓ) hP hQ
  have hmap := wassersteinE_map_clm_le ℓ 1 le_rfl P Q
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  refine ENNReal.div_le_of_le_mul ?_
  calc ENNReal.ofReal |∫ x, x ∂(P.map ℓ) - ∫ x, x ∂(Q.map ℓ)|
      ≤ wassersteinE 1 (P.map ℓ) (Q.map ℓ) := hA2
    _ ≤ ENNReal.ofReal ‖ℓ‖ * wassersteinE 1 P Q := hmap
    _ ≤ wassersteinE 1 P Q * ENNReal.ofReal (‖ℓ‖ + 1) := by
          rw [mul_comm]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (by linarith [norm_nonneg ℓ]))

end HRS.MH.MfclP
