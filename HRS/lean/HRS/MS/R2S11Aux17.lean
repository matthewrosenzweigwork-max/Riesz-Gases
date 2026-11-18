import HRS.MS.R2S11Aux16
import HRS.Whole.Window

/-!
# S11.2: the frozen `r2_two_parameter_edgeworth` from its part (a)

`s11_two_param_of_a`: parts (b) and (c) of `r2_two_parameter_edgeworth` follow from part (a) (the bound with constants `c, C` chosen before `ρβ`),
by multiplying (a) by `√N` and `s11_exp_tendsto_of_ge_log`, `s11_exp_tendsto_of_sqrt` (`R2S11Aux16`).  Part (a) itself follows from the conclusion of
`r2_tensor_relaxation` and a Banach-space Gaussian covariance comparison (plan, S11.2 packets D2, G).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s11_two_param_of_a (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (a β γ : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam)
    (hA : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ →
      IsR2Poincare (HRS.Whole.withDensityReal ρβ) lam →
      ∀ (κγ : ℝ → projTensor (R2X d T) 3) (κβ : projTensor (R2X d T) 3),
        (∀ u : ℝ, 0 ≤ u → IsR2PathCubic d s a β γ ρβ T u (κγ u)) → IsR2PathCubic d s a β β ρβ T 0 κβ →
        ∀ {Ω' Ω'' : Type} [MeasurableSpace Ω'] [MeasurableSpace Ω''] (P' : Measure Ω') (P'' : Measure Ω'')
          [IsProbabilityMeasure P'] [IsProbabilityMeasure P''] (Zγ : ℝ → Ω' → OscDual d (wholeSpaceIndex d : ℝ))
          (Zβ : ℝ → Ω'' → OscDual d (wholeSpaceIndex d : ℝ)),
        (∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρβ) γ) Zγ) →
        (∀ T' : ℝ, IsLinearGaussianEvolutionW P'' ((quadraticGradientDyn d s a β).coeff (fun _ => ρβ))
          (wholeSpaceIndex d) β⁻¹ T' (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρβ) β) Zβ) →
        (∀ {N : ℕ}, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
          (εN : ℝ),
          IsR2Realization d s a β P X₀ W X →
          law P X₀ = HRS.Whole.modulatedGibbs (rieszKernel d s) N γ (HRS.Whole.withDensityReal ρβ) →
          (∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
            |Real.sqrt N * (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P -
                ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T u Zγ ζ) ∂P') -
              (1 / 6) * r2CubicExpect P' (processWindow (wholeSpaceIndex d) T u Zγ) (κγ u) Φ| ≤ εN) →
          ∀ u : ℝ, 0 ≤ u → ∀ Φ ∈ CbUnitBall (R2X d T) 5,
            |∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T u P X ζ) ∂P -
                ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T 0 Zβ ζ) ∂P'' -
              (1 / (6 * Real.sqrt N)) * r2CubicExpect P'' (processWindow (wholeSpaceIndex d) T 0 Zβ) κβ Φ| ≤
              εN / Real.sqrt N + C * Real.exp (-2 * (lam / β) * u) +
                C / Real.sqrt N * Real.exp (-c * u))) :
    type_of% (r2_two_parameter_edgeworth hd s hs0 hs a β γ ha hβ hγ hγs T hT lam hlam) := by
  obtain ⟨c, hc, C, hAll⟩ := hA
  refine ⟨c, hc, C, fun ρβ hρ hP κγ κβ h1 h2 Ω' Ω'' _ _ P' P'' _ _ Zγ Zβ hZ1 hZ2 => ?_⟩
  refine ⟨hAll ρβ hρ hP κγ κβ h1 h2 P' P'' Zγ Zβ hZ1 hZ2, ?_⟩
  intro Ω _ P _ X₀ W X εN hεN hreal uN hu0 hcase ε hε
  have hκ : 0 < lam / β := div_pos hlam hβ
  have hT1T2 : Tendsto (fun N : ℕ => Real.sqrt N * Real.exp (-2 * (lam / β) * uN N)) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => Real.exp (-c * uN N)) atTop (𝓝 0) := by
    rcases hcase with h | ⟨δ, hδ, hu⟩
    · exact ⟨h, s11_exp_tendsto_of_sqrt hκ hc uN h⟩
    · exact s11_exp_tendsto_of_ge_log hκ hδ hc uN hu
  obtain ⟨hT1, hT2⟩ := hT1T2
  have hlim : Tendsto (fun N : ℕ => εN N + |C| * (Real.sqrt N * Real.exp (-2 * (lam / β) * uN N)) +
      |C| * Real.exp (-c * uN N)) atTop (𝓝 0) := by
    have := (hεN.add (hT1.const_mul |C|)).add (hT2.const_mul |C|)
    simpa using this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max N₀ 2, fun N hN hN2 Φ hΦ => ?_⟩
  have hN₀' : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN2' : 2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hr1, hr2, hr3⟩ := hreal N hN2'
  have hb := hAll ρβ hρ hP κγ κβ h1 h2 P' P'' Zγ Zβ hZ1 hZ2 (N := N) hN2' (P N) (X₀ N) (W N) (X N) (εN N) hr1 hr2 hr3 (uN N) (hu0 N) Φ hΦ
  have hf := hN₀ N hN₀'
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  set x : ℝ := (∫ ζ, Φ (zetaPathW (wholeSpaceIndex d) T (uN N) (P N) (X N) ζ) ∂(P N)) -
    ∫ ζ, Φ (processWindow (wholeSpaceIndex d) T 0 Zβ ζ) ∂P'' with hx
  set E : ℝ := r2CubicExpect P'' (processWindow (wholeSpaceIndex d) T 0 Zβ) κβ Φ with hE
  have e1 : Real.sqrt N * (x - 1 / (6 * Real.sqrt N) * E) = Real.sqrt N * x - 1 / 6 * E := by
    field_simp
  have e2 : |Real.sqrt N * x - 1 / 6 * E| = Real.sqrt N * |x - 1 / (6 * Real.sqrt N) * E| := by
    rw [← e1, abs_mul, abs_of_pos hsN]
  have h3 : Real.sqrt N * (εN N / Real.sqrt N + C * Real.exp (-2 * (lam / β) * uN N) +
      C / Real.sqrt N * Real.exp (-c * uN N)) =
      εN N + C * (Real.sqrt N * Real.exp (-2 * (lam / β) * uN N)) + C * Real.exp (-c * uN N) := by
    field_simp
  have h4 : εN N + C * (Real.sqrt N * Real.exp (-2 * (lam / β) * uN N)) + C * Real.exp (-c * uN N) ≤
      εN N + |C| * (Real.sqrt N * Real.exp (-2 * (lam / β) * uN N)) + |C| * Real.exp (-c * uN N) := by
    have a1 : 0 ≤ Real.sqrt N * Real.exp (-2 * (lam / β) * uN N) := by positivity
    have a2 : 0 ≤ Real.exp (-c * uN N) := (Real.exp_pos _).le
    nlinarith [le_abs_self C, mul_le_mul_of_nonneg_right (le_abs_self C) a1,
      mul_le_mul_of_nonneg_right (le_abs_self C) a2]
  have hfin : |Real.sqrt N * x - 1 / 6 * E| ≤ ε := by
    rw [e2]
    calc Real.sqrt N * |x - 1 / (6 * Real.sqrt N) * E| ≤ Real.sqrt N * (εN N / Real.sqrt N +
          C * Real.exp (-2 * (lam / β) * uN N) + C / Real.sqrt N * Real.exp (-c * uN N)) :=
          mul_le_mul_of_nonneg_left hb hsN.le
      _ ≤ _ := by rw [h3]; linarith
  exact hfin

end HRS.MS.R2S11
