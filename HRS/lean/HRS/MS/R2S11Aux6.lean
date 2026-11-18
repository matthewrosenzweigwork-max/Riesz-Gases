import HRS.MS.R2S11Aux5
import HRS.MS.R2S11Aux4
import HRS.MS.MovEntAux1
import HRS.MS.S113Exponent
import HRS.MS.S113ActualDensity

/-!
# S11.4 item (1): the actual-law density bound from the S11.3 interface, with a class-uniform exponent

* `s11_L_le`, `s11_L_integral_le`: for a member of the small class, `L(t) = ‖∇u^t‖_∞ ≤ C₁ ε_* e^{-ct}` and `∫_0^∞ L ≤ C₁ ε_*/c`
  (decay clause of `MovNonlinearConclusion`, `j ≥ 1`);
* `S11ActDens`: item (1) of `r2_moving_moment_transfer` as a proposition;
* `s11_item1_of_Lp`: item (1) from the conclusion of `r2_moving_Lp` (clause (2), with `p₀ = 1 + min 1 (γ/(2β))` resp. `1 + min 1 (a_*/(2β))`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- Item (1) of `r2_moving_moment_transfer`. -/
def S11ActDens (d : ℕ) (s q β γ : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ pinf K : ℝ) : Prop :=
  ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      MovParticleSetup P d s q β N X₀ W X → MovPrepared d s N γ (HRS.Whole.withDensityReal (ρ 0)) (P.map X₀) →
      ∀ t : ℝ, 0 ≤ t → HasR2ActualDensity s β pinf K (HRS.Whole.withDensityReal (ρ t)) (P.map (X t.toNNReal))

theorem s11_L_le {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) (hC₁ : 0 < C₁) (hε : 0 < εstar)
    (hc₀ : 0 ≤ c₀) {f0 : Euc d → ℝ} (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {t : ℝ} (ht : 0 ≤ t) :
    r2MovL d s q β ρ t ≤ C₁ * εstar * Real.exp (-c * t) := by
  obtain ⟨-, -, -, hdec⟩ := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ hc₀ t ht
  obtain ⟨-, -, -, hcb⟩ := hdec t ht
  have hΛ0 : 0 ≤ C₁ * εstar * Real.exp (-c * t) := by positivity
  have h1 : cbNormVecE j (movU d s q β (ρ t)) ≤ ENNReal.ofReal (C₁ * εstar * Real.exp (-c * t)) :=
    le_trans le_add_self hcb
  unfold r2MovL
  refine ENNReal.toReal_le_of_le_ofReal hΛ0 (iSup_le fun x => ?_)
  apply ENNReal.ofReal_le_ofReal
  have := HRS.MS.R2S11.s11_cbVec_bound h1 (i := 1) hj x
  rw [norm_iteratedFDeriv_one] at this
  exact this.trans (max_eq_left hΛ0).le

theorem s11_L_integral_le {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j)
    (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) (hC₁ : 0 < C₁) (hε : 0 < εstar)
    (hc : 0 < c) (hc₀ : 0 ≤ c₀) {f0 : Euc d → ℝ} (hf0 : MovInitialClass ρ₀ j m εstar f0)
    {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ)
    (hLi : Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ)))) :
    (∫ t in Set.Ioi (0 : ℝ), r2MovL d s q β ρ t) ≤ C₁ * εstar / c := by
  have hneg : -c < 0 := by linarith
  have hint : IntegrableOn (fun t : ℝ => C₁ * εstar * Real.exp (-c * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul _
  have hval : ∫ t in Set.Ioi (0 : ℝ), C₁ * εstar * Real.exp (-c * t) = C₁ * εstar / c := by
    rw [integral_const_mul, integral_exp_mul_Ioi hneg 0]
    field_simp
    simp
  rw [← hval]
  refine integral_mono_of_nonneg ?_ hint ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t _ => ENNReal.toReal_nonneg)
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
      s11_L_le hj hNL hC₁ hε hc₀ hf0 hρ (le_of_lt ht))

end HRS.MS.R2S11
