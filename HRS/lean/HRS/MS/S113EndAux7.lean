import HRS.MS.S113EndAux5
import HRS.MS.S113EndAux6
import HRS.MS.R2S11Aux6

/-!
# S11.3 endpoint (worker S113X), part 7: finiteness and integrability of `L(t) = ‖∇u^t‖_∞`; the `L^{p_∞}` norm bound
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s113x_L_sup_lt_top {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) (hC₁ : 0 < C₁) (hε : 0 < εstar)
    (hc₀ : 0 < c₀) {f0 : Euc d → ℝ} (hf0 : MovInitialClass ρ₀ j m εstar f0)
    {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {t : ℝ} (ht : 0 ≤ t) :
    (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖) < ⊤ := by
  obtain ⟨-, -, -, hdec⟩ := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ hc₀.le t ht
  obtain ⟨-, -, -, hcb⟩ := hdec t ht
  have hΛ0 : 0 ≤ C₁ * εstar * Real.exp (-c * t) := by positivity
  have h1 : cbNormVecE j (movU d s q β (ρ t)) ≤ ENNReal.ofReal (C₁ * εstar * Real.exp (-c * t)) :=
    le_trans le_add_self hcb
  refine lt_of_le_of_lt (iSup_le fun x => ?_) (ENNReal.ofReal_lt_top (r := C₁ * εstar * Real.exp (-c * t)))
  apply ENNReal.ofReal_le_ofReal
  have := HRS.MS.R2S11.s11_cbVec_bound h1 (i := 1) hj x
  rw [norm_iteratedFDeriv_one] at this
  exact this.trans (max_eq_left hΛ0).le

theorem s113x_L_props {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) (hC₁ : 0 < C₁) (hε : 0 < εstar)
    (hc : 0 < c) (hc₀ : 0 < c₀) {f0 : Euc d → ℝ} (hf0 : MovInitialClass ρ₀ j m εstar f0)
    {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ)
    (hmeas : AEStronglyMeasurable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∀ t : ℝ, 0 ≤ t → (⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖) < ⊤) ∧
      Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine ⟨fun t ht => s113x_L_sup_lt_top hj hNL hC₁ hε hc₀ hf0 hρ ht, ?_⟩
  have hneg : -c < 0 := by linarith
  have hint : IntegrableOn (fun t : ℝ => C₁ * εstar * Real.exp (-c * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul _
  refine Integrable.mono' hint hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_of_nonneg (by unfold r2MovL; exact ENNReal.toReal_nonneg)]
  exact HRS.MS.R2S11.s11_L_le hj hNL hC₁ hε hc₀.le hf0 hρ (le_of_lt ht)

/-- `‖h‖_{L^{p_∞}} ≤ K` from the power moment at an exponent `p ≥ p_∞ > 0` on a probability space, `K ≥ 1`. -/
theorem s113x_eLpNorm_le {α : Type*} [MeasurableSpace α] (Q : Measure α) [IsProbabilityMeasure Q] (h : α → ℝ)
    (hh : Measurable h) (hh0 : ∀ x, 0 ≤ h x) {pinf p K : ℝ} (hpinf : 1 ≤ pinf) (hle : pinf ≤ p) (hK : 1 ≤ K)
    (hmom : ∫⁻ x, ENNReal.ofReal (h x ^ p) ∂Q ≤ ENNReal.ofReal K) :
    eLpNorm h (ENNReal.ofReal pinf) Q ≤ ENNReal.ofReal K := by
  have hp1 : 1 ≤ p := hpinf.trans hle
  have hp0 : 0 < p := by linarith
  calc eLpNorm h (ENNReal.ofReal pinf) Q ≤ eLpNorm h (ENNReal.ofReal p) Q :=
        eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hle)
    _ = (∫⁻ x, ‖h x‖ₑ ^ p ∂Q) ^ (1 / p) := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
          hh.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    _ = (∫⁻ x, ENNReal.ofReal (h x ^ p) ∂Q) ^ (1 / p) := by
        congr 1
        refine lintegral_congr fun x => ?_
        rw [← ofReal_norm, Real.norm_of_nonneg (hh0 x), ENNReal.ofReal_rpow_of_nonneg (hh0 x) hp0.le]
    _ ≤ (ENNReal.ofReal K) ^ (1 / p) := ENNReal.rpow_le_rpow hmom (by positivity)
    _ ≤ (ENNReal.ofReal K) ^ (1 : ℝ) := by
        refine ENNReal.rpow_le_rpow_of_exponent_le ?_ ?_
        · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK
        · rw [div_le_one hp0]; exact hp1
    _ = ENNReal.ofReal K := ENNReal.rpow_one _

end HRS.MS.S113BD
