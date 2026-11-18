import HRS.MS.S113Exponent
import HRS.Whole.Round2

/-!
# S11.3.U2 (GPT-6 Pro breakdown, packet U2): the fixed-exponent `HasR2ActualDensity` from a variable power moment
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

theorem s113_actualDensity_of_variable_power
    (d N : ℕ) (s β : ℝ) (ρ : ℝ → HRS.Euc d → ℝ)
    (f : Measure (HRS.Whole.EucConfig d N)) [IsProbabilityMeasure f]
    (cL p₀ B K t : ℝ) (hcL : 0 < cL) (hp₀ : 1 < p₀)
    (hB : 0 ≤ B) (hK : 1 ≤ K) (ht : 0 ≤ t)
    (L : ℝ → ℝ) (hL0 : ∀ u, 0 ≤ u → 0 ≤ L u)
    (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    (hLB : (∫ u in Set.Ioi (0 : ℝ), L u) ≤ B)
    [IsProbabilityMeasure
      (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal (ρ t)))]
    (hac : f ≪ HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal (ρ t)))
    (hpow : HRS.Whole.r2MovPowerMoment d s β ρ N f t
      (HRS.Whole.r2MovExponent cL p₀ L t) ≤ ENNReal.ofReal K) :
    let pstar := (1 - (1 - p₀⁻¹) * Real.exp (-(cL⁻¹) * B))⁻¹
    1 < pstar ∧ HRS.Whole.HasR2ActualDensity s β pstar K
      (HRS.Whole.withDensityReal (ρ t)) f := by
  intro pstar
  obtain ⟨h1, h2, h3⟩ := s113_uniform_exponent cL p₀ B hcL hp₀ hB L hL0 hLi hLB
  obtain ⟨h4, -⟩ := h3 t ht
  refine ⟨h1, inferInstance, hac, ?_⟩
  set Q := HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t)) with hQ
  set p := HRS.Whole.r2MovExponent cL p₀ L t with hp
  have hpp : pstar ≤ p := h2.trans h4
  have hp1 : 1 < p := lt_of_lt_of_le h1 hpp
  have hp0 : 0 < p := by linarith
  set h : HRS.Whole.EucConfig d N → ℝ := fun X => (f.rnDeriv Q X).toReal with hh
  have hm : AEStronglyMeasurable h Q :=
    (Measure.measurable_rnDeriv f Q).ennreal_toReal.aestronglyMeasurable
  calc eLpNorm h (ENNReal.ofReal pstar) Q ≤ eLpNorm h (ENNReal.ofReal p) Q :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpp)
    _ = (∫⁻ x, ‖h x‖ₑ ^ p ∂Q) ^ (1 / p) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hm,
          ENNReal.toReal_ofReal hp0.le]
    _ = (HRS.Whole.r2MovPowerMoment d s β ρ N f t p) ^ (1 / p) := by
        congr 1
        unfold HRS.Whole.r2MovPowerMoment HRS.Whole.r2MovRatio
        refine lintegral_congr fun x => ?_
        rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp0.le]
    _ ≤ (ENNReal.ofReal K) ^ (1 / p) := ENNReal.rpow_le_rpow hpow (by positivity)
    _ = ENNReal.ofReal (K ^ (1 / p)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by positivity)]
    _ ≤ ENNReal.ofReal K := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc K ^ (1 / p) ≤ K ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hK (by rw [div_le_one hp0]; linarith)
          _ = K := Real.rpow_one K

end HRS.MS.S113BD
