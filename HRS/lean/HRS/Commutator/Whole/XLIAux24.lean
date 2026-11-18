import HRS.Commutator.Whole.XLIAux23

/-!
# X-LI part 24: `L^p` bounds for convolutions and the Bessel potential bound `‖f‖_p ≲ ‖J^α f‖_p`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Young's inequality for an integrable kernel -/
lemma eLpNorm_cv_le {K F : 𝔼 → ℂ} (hKm : Measurable K) (hFm : Measurable F) {p : ℝ≥0∞}
    (hp : 1 ≤ p) :
    eLpNorm (cv K F) p volume ≤ (∫⁻ z, ‖K z‖ₑ) * eLpNorm F p volume := by
  by_cases hpt : p = ⊤
  · subst hpt
    rw [eLpNorm_exponent_top, eLpNorm_exponent_top, eLpNormEssSup, eLpNormEssSup]
    have hae : ∀ x, ‖cv K F x‖ₑ ≤ (∫⁻ z, ‖K z‖ₑ) * essSup (fun y => ‖F y‖ₑ) volume := by
      intro x
      refine (enorm_cv_le K F x).trans ?_
      have hq : ∀ᵐ z ∂(volume : Measure 𝔼), ‖F (x - z)‖ₑ ≤ essSup (fun y => ‖F y‖ₑ) volume := by
        have h0 : ∀ᵐ y ∂(volume : Measure 𝔼), ‖F y‖ₑ ≤ essSup (fun y => ‖F y‖ₑ) volume :=
          ENNReal.ae_le_essSup _
        exact (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae h0
      calc ∫⁻ z, ‖K z‖ₑ * ‖F (x - z)‖ₑ
          ≤ ∫⁻ z, ‖K z‖ₑ * essSup (fun y => ‖F y‖ₑ) volume :=
            lintegral_mono_ae (hq.mono fun z hz => mul_le_mul_right hz _)
        _ = _ := by
            exact lintegral_mul_const'' _ hKm.enorm.aemeasurable
    · exact essSup_le_of_ae_le _ (Eventually.of_forall hae)
    all_goals first | exact hFm.aestronglyMeasurable | exact (measurable_cv hKm hFm).aestronglyMeasurable
  · have hp0 : p ≠ 0 := by
      intro h; rw [h] at hp; simp at hp
    have hpr : 1 ≤ p.toReal := by
      have := ENNReal.toReal_mono hpt hp
      simpa using this
    have hpr0 : 0 < p.toReal := by linarith
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
    swap
    · exact hFm.aestronglyMeasurable
    swap
    · exact (measurable_cv hKm hFm).aestronglyMeasurable
    have hy := young_lintegral (a := fun z => ‖K z‖ₑ) (b := fun z => ‖F z‖ₑ) hKm.enorm hFm.enorm hpr
    have h1 : ∫⁻ x, ‖cv K F x‖ₑ ^ p.toReal ≤ (∫⁻ z, ‖K z‖ₑ) ^ p.toReal * ∫⁻ x, ‖F x‖ₑ ^ p.toReal := by
      refine le_trans (lintegral_mono fun x => ?_) hy
      exact ENNReal.rpow_le_rpow (enorm_cv_le K F x) hpr0.le
    calc (∫⁻ x, ‖cv K F x‖ₑ ^ p.toReal) ^ (1 / p.toReal)
        ≤ ((∫⁻ z, ‖K z‖ₑ) ^ p.toReal * ∫⁻ x, ‖F x‖ₑ ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.rpow_le_rpow h1 (by positivity)
      _ = (∫⁻ z, ‖K z‖ₑ) * (∫⁻ x, ‖F x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
          have : p.toReal * (1 / p.toReal) = 1 := by field_simp
          rw [this, ENNReal.rpow_one]

lemma enorm_le_eLpNorm_top (F : SchwartzMap 𝔼 ℂ) (x : 𝔼) : ‖F x‖ₑ ≤ eLpNorm (⇑F) ⊤ volume := by
  by_contra h
  rw [not_le] at h
  have hopen : IsOpen {y : 𝔼 | eLpNorm (⇑F) ⊤ volume < ‖F y‖ₑ} :=
    isOpen_lt continuous_const (continuous_enorm.comp F.continuous)
  have hnull : volume {y : 𝔼 | eLpNorm (⇑F) ⊤ volume < ‖F y‖ₑ} = 0 := by
    have h0 := enorm_ae_le_eLpNormEssSup (⇑F) (volume : Measure 𝔼)
    rw [eLpNorm_exponent_top F.continuous.aestronglyMeasurable]
    rw [ae_iff] at h0
    simpa [not_le] using h0
  have := (hopen.measure_eq_zero_iff volume).1 hnull
  exact (Set.eq_empty_iff_forall_notMem.1 this x) h

lemma mulS_one (f : SchwartzMap 𝔼 ℂ) (h : (fun _ : 𝔼 => (1 : ℂ)).HasTemperateGrowth) :
    ⇑(mulS (fun _ : 𝔼 => (1 : ℂ)) h f) = ⇑f := by
  funext x
  rw [mulS_apply]
  simp only [one_mul]
  have h1 : (𝓕⁻ (𝓕 f) : SchwartzMap 𝔼 ℂ) = f := FourierTransform.fourierInv_fourier_eq f
  have h2 := SchwartzMap.fourierInv_coe (𝓕 f)
  rw [h1, SchwartzMap.fourier_coe] at h2
  exact (congrFun h2 x).symm

section BP

variable (α : ℝ)

lemma Fm_inv (f : SchwartzMap 𝔼 ℂ) :
    ⇑(mulS (bsymX (-α)) (bsymX_temperate (-α)) (Fm α f)) = ⇑f := by
  unfold Fm
  rw [mulS_mulS _ _ (bsymX_temperate (-α)) (bsymX_temperate α)
    ((bsymX_temperate (-α)).mul (bsymX_temperate α))]
  have hsym : (fun ξ : 𝔼 => bsymX (-α) ξ * bsymX α ξ) = fun _ => (1 : ℂ) := by
    funext ξ
    rw [bsymX_mul]
    simp [bsymX_zero]
  rw [mulS_congr hsym ((bsymX_temperate (-α)).mul (bsymX_temperate α))
    (Function.HasTemperateGrowth.const (1 : ℂ))]
  exact mulS_one f _

end BP

end HRS.Commutator.Whole.XLI
