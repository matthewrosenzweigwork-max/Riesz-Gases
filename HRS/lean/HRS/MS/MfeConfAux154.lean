import HRS.MS.MfeConfAux153

/-!
# S.B.1 (SB5), packet R3c (part 4): removing the conditioning
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

section L1

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
  {A : ℕ → Set Ω}

/-- a function bounded below with uniformly bounded conditioned means is integrable under the limit law -/
theorem sb1_unc_L1 (hA : ∀ j, MeasurableSet (A j)) (hmono : Monotone A) (hcov : ∀ᵐ ζ ∂Pm, ∃ j, ζ ∈ A j)
    (hpos : ∀ j, Pm (A j) ≠ 0) {Y : Ω → α} (hY : Measurable Y) {f : α → ℝ} (hf : Measurable f) {c B : ℝ}
    (hc : ∀ x, -c ≤ f x) (hB : 0 ≤ B) (hi : ∀ j, Integrable f ((ProbabilityTheory.cond Pm (A j)).map Y))
    (hb : ∀ j, ∫ x, f x ∂((ProbabilityTheory.cond Pm (A j)).map Y) + c ≤ B) : Integrable f (Pm.map Y) := by
  have hFm : Measurable (fun ζ => f (Y ζ) + c) := (hf.comp hY).add_const c
  have hF0 : ∀ ζ, 0 ≤ f (Y ζ) + c := fun ζ => by linarith [hc (Y ζ)]
  have hIi : ∀ j, IntegrableOn (fun ζ => f (Y ζ)) (A j) Pm := fun j =>
    (sb1_cond_integrable (hA j) (hpos j) hY hf).1 (hi j)
  have hmain := sb1_cond_L1 hA hmono hcov hFm hF0 (B := B) (fun j => (hIi j).add (integrableOn_const (by simp)))
    (fun j => by
      have hp0 : 0 < (Pm (A j)).toReal := ENNReal.toReal_pos (hpos j) (measure_ne_top _ _)
      have hp1 : (Pm (A j)).toReal ≤ 1 := by
        have := prob_le_one (μ := Pm) (s := A j)
        simpa using ENNReal.toReal_mono (by simp) this
      rw [integral_add (hIi j) (integrableOn_const (by simp)), setIntegral_const]
      have e := sb1_cond_integral (Pm := Pm) (A := A j) hY hf
      have h2 := hb j
      rw [e] at h2
      have e2 : ∫ ζ in A j, f (Y ζ) ∂Pm = (Pm (A j)).toReal * ((Pm (A j)).toReal⁻¹ * ∫ ζ in A j, f (Y ζ) ∂Pm) := by
        field_simp
      simp only [Measure.real, smul_eq_mul]
      rw [e2]
      nlinarith)
  have h3 : Integrable (fun ζ => f (Y ζ)) Pm := by
    refine (hmain.1.sub (integrable_const c)).congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp
  exact (integrable_map_measure hf.aestronglyMeasurable hY.aemeasurable).2 h3

end L1

end HRS.MS.MfeConf
