import HRS.MS.R26T8AP17g

/-!
# S8.2 local Newton layer, packet T8A.P17 (part h): measure bookkeeping and the centred pair
`r26t8a_p17_integral_wd`, `r26t8a_p17_integrable_wd`: `∫ g d(withDensityReal rho) = ∫ rho g` and integrability.
`r26t8a_p17_center_form`: for symmetric `k`, `r2CenterKernel μ k x y = k x y - a x - a y + ∫ a dμ`.
`r26t8a_p17_canonical`: for a symmetric kernel with integrable rows and integrable row-mean `a`, `(1/2) * r2CenterKernel μ k` is a `CanonicalPair`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff ENNReal
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p17_integral_wd {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (g : Euc d → ℝ) :
    ∫ y, g y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y * g y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (hρ.measurable.ennreal_ofReal)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

theorem r26t8a_p17_integrable_wd {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {g : Euc d → ℝ}
    (hg : Integrable (fun y => ρ y * g y)) : Integrable g (HRS.Whole.withDensityReal ρ) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' (hρ.measurable.ennreal_ofReal)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine hg.congr (Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg y)]

theorem r26t8a_p17_center_form (μ : Measure (Euc d)) (k : Euc d → Euc d → ℝ) (hk : ∀ x y, k x y = k y x) (x y : Euc d) :
    r2CenterKernel μ k x y = k x y - ∫ y', k x y' ∂μ - ∫ y', k y y' ∂μ +
      ∫ x', ∫ y', k x' y' ∂μ ∂μ := by
  unfold r2CenterKernel
  have : ∫ x', k x' y ∂μ = ∫ y', k y y' ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x' => hk x' y)
  rw [this]

theorem r26t8a_p17_canonical (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (k : Euc d → Euc d → ℝ)
    (hk : ∀ x y, k x y = k y x) (hrow : ∀ x, Integrable (k x) μ)
    (ha : Integrable (fun x => ∫ y', k x y' ∂μ) μ) :
    CanonicalPair μ (fun x y => (1 / 2 : ℝ) * r2CenterKernel μ k x y) := by
  set a : Euc d → ℝ := fun x => ∫ y', k x y' ∂μ with hadef
  set c0 : ℝ := ∫ x', a x' ∂μ with hc0
  have hform : ∀ x y, (1 / 2 : ℝ) * r2CenterKernel μ k x y = (1 / 2 : ℝ) * (k x y - a x - a y + c0) := by
    intro x y; rw [r26t8a_p17_center_form μ k hk]
  have hcol : ∀ y, ∫ x, k x y ∂μ = a y := fun y => integral_congr_ae (Eventually.of_forall fun x => hk x y)
  have hrow' : ∀ y, Integrable (fun x => k x y) μ := fun y => (hrow y).congr (Eventually.of_forall fun x => hk y x)
  refine ⟨fun y => ?_, fun x => ?_, fun y => ?_, fun x => ?_⟩
  · simp_rw [hform]
    exact (((hrow' y).sub ha).sub (integrable_const _)).add (integrable_const _) |>.const_mul _
  · simp_rw [hform]
    exact (((hrow x).sub (integrable_const _)).sub ha).add (integrable_const _) |>.const_mul _
  · simp_rw [hform]
    have i12 : Integrable (fun x => k x y - a x - a y) μ := ((hrow' y).sub ha).sub (integrable_const _)
    have e : ∫ x, (k x y - a x - a y + c0) ∂μ = (∫ x, k x y ∂μ) - c0 - a y + c0 := by
      rw [integral_add (f := fun x => k x y - a x - a y) (g := fun _ => c0) i12 (integrable_const _),
        integral_sub (f := fun x => k x y - a x) (g := fun _ => a y) ((hrow' y).sub ha) (integrable_const _),
        integral_sub (hrow' y) ha]
      simp [hc0]
    rw [integral_const_mul, e, hcol y]; ring
  · simp_rw [hform]
    have i12 : Integrable (fun y' => k x y' - a x - a y') μ := ((hrow x).sub (integrable_const _)).sub ha
    have e : ∫ y', (k x y' - a x - a y' + c0) ∂μ = (∫ y', k x y' ∂μ) - a x - c0 + c0 := by
      rw [integral_add (f := fun y' => k x y' - a x - a y') (g := fun _ => c0) i12 (integrable_const _),
        integral_sub (f := fun y' => k x y' - a x) (g := a) ((hrow x).sub (integrable_const _)) ha,
        integral_sub (hrow x) (integrable_const _)]
      simp [hc0]
    rw [integral_const_mul, e]; simp [hadef]

end HRS.MS.R26T8A
