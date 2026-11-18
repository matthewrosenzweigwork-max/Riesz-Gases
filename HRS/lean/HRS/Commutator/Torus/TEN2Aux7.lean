import HRS.Commutator.Torus.TEN2Aux6

/-!
# Torus energy layer (packet T-EN2), helper part 7: Hölder for the one-point convolution on `𝕋^d`

Prefix `ten2_`.  `∫ f(z-y)ρ(y)dy ≤ ‖f‖_q‖ρ‖_p` and the resulting bound for `f = f_η^𝕋`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

theorem ten2_holder_T {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) (f ρ : Torus d → ℝ)
    (hfq : MemLp f q volume) (hρ : BddDensityT ρ) (z : Torus d)
    (hI : Integrable (fun y => f (z - y) * ρ y)) :
    ∫ y, f (z - y) * ρ y ≤ (eLpNorm f q volume).toReal * (eLpNorm ρ p volume).toReal := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hT1 : ENNReal.HolderTriple q p 1 := ENNReal.holderConjugate_iff.2 (by rw [add_comm]; exact hpq)
  have hρp : MemLp ρ p volume :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable B
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hfz : eLpNorm (fun y => f (z - y)) q volume = eLpNorm f q volume :=
    eLpNorm_comp_measurePreserving hfq.aestronglyMeasurable
      ((volume : Measure (Torus d)).measurePreserving_sub_left z)
  have hH : eLpNorm (fun y => f (z - y) * ρ y) 1 volume ≤
      eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume := by
    have hfzm : AEStronglyMeasurable (fun y => f (z - y)) volume :=
      hfq.aestronglyMeasurable.comp_measurePreserving
        ((volume : Measure (Torus d)).measurePreserving_sub_left z)
    have := MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_enorm (p := q) (q := p) (r := 1)
      (fun a b : ℝ => a * b) (1 : ℝ≥0∞) (continuous_mul) hfzm hρp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simp [enorm_mul])
    simpa using this
  have hfin1 : eLpNorm (fun y => f (z - y)) q volume ≠ ⊤ := by
    rw [hfz]; exact hfq.eLpNorm_lt_top.ne
  have hfin2 : eLpNorm ρ p volume ≠ ⊤ := hρp.eLpNorm_lt_top.ne
  have hstep1 : ∫ y, f (z - y) * ρ y ≤ ∫ y, ‖f (z - y) * ρ y‖ :=
    integral_mono hI hI.norm fun y => Real.le_norm_self _
  have hstep2 : ∫ y, ‖f (z - y) * ρ y‖ = (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm hI.aestronglyMeasurable,
      integral_norm_eq_lintegral_enorm hI.aestronglyMeasurable]
  have hstep3 : (eLpNorm (fun y => f (z - y) * ρ y) 1 volume).toReal ≤
      (eLpNorm (fun y => f (z - y)) q volume * eLpNorm ρ p volume).toReal := by
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top hfin1 hfin2) ?_
    simpa using hH
  rw [hfz] at hstep3
  rw [ENNReal.toReal_mul] at hstep3
  linarith

/-- The cross term: `(1/N)∑_i ∫ f_η^𝕋(X_i - y)ρ(y)dy ≤ C η^{d/q-s} ‖ρ‖_p`. -/
theorem ten2_cross_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {p q : ℝ≥0∞}
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ ρ : Torus d → ℝ, BddDensityT ρ → ∀ z : Torus d,
      ∫ y, fTorus s η (z - y) * ρ y ≤ C * η ^ ((d : ℝ) / q.toReal - s) * normT p ρ := by
  obtain ⟨C, hC0, hC⟩ := ten2_fTorus_Lq (s := s) hd hs0 hsd hp hpq
  refine ⟨C, hC0, fun η hη hη1 ρ hρ z => ?_⟩
  obtain ⟨hmem, hnorm⟩ := hC η hη hη1
  have hR : Integrable (periodicRiesz d s) :=
    HRS.KernelAux.integrable_periodicRiesz (by omega) hs0 (by linarith)
  obtain ⟨-, -, -, hlift⟩ := tpos_coef_formula hd hs0 hsd η hη
  have hG : Continuous (gTorus s η) := HRS.Torus.continuous_of_continuous_lift hlift
  have hf : Integrable (fTorus s η) := ten_fTorus_integrable hR hG (by omega)
  have h1 := ten2_holder_T hpq (fTorus s η) ρ hmem hρ z (ten_sec_integrable hf hρ z)
  have hnp : 0 ≤ (eLpNorm ρ p volume).toReal := ENNReal.toReal_nonneg
  calc ∫ y, fTorus s η (z - y) * ρ y
      ≤ (eLpNorm (fTorus s η) q volume).toReal * (eLpNorm ρ p volume).toReal := h1
    _ ≤ (C * η ^ ((d : ℝ) / q.toReal - s)) * (eLpNorm ρ p volume).toReal :=
        mul_le_mul_of_nonneg_right hnorm hnp
    _ = C * η ^ ((d : ℝ) / q.toReal - s) * normT p ρ := rfl

end HRS.Commutator.TorusNote
