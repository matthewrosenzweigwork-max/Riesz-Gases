import HRS.MS.R2ChaosAux13

/-!
# HRS.MS.R2ChaosAux14 -- joint measurability of `pairEnergy (h t)` and of `r2QuadFluct`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Meas

variable {N : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

/-- `(t, X) ↦ pairEnergy (h t) X μ` is jointly measurable for a jointly measurable kernel family. -/
theorem s94_pairEnergy_measurable {h : ℝ → Euc d → Euc d → ℝ}
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × EucConfig d N => pairEnergy (h q.1) q.2 μ := by
  have hA : ∀ i j : Fin N, Measurable fun q : ℝ × EucConfig d N => h q.1 (q.2 i) (q.2 j) := fun i j =>
    Measurable.comp (g := fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
      (f := fun q : ℝ × EucConfig d N => (q.1, q.2 i, q.2 j)) hmeas (by fun_prop)
  have hB : ∀ i : Fin N, Measurable fun q : ℝ × EucConfig d N => ∫ y, h q.1 (q.2 i) y ∂μ := fun i => by
    have h3 : Measurable fun p : (ℝ × Euc d) × Euc d => h p.1.1 p.1.2 p.2 :=
      hmeas.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have := (h3.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
    exact this.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hC : Measurable fun t : ℝ => ∫ x, ∫ y, h t x y ∂μ ∂μ := by
    have h3 : Measurable fun p : (ℝ × Euc d) × Euc d => h p.1.1 p.1.2 p.2 :=
      hmeas.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have h4 : Measurable fun p : ℝ × Euc d => ∫ y, h p.1 p.2 y ∂μ :=
      (h3.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
    exact (h4.stronglyMeasurable.integral_prod_right' (ν := μ) |>.measurable)
  unfold pairEnergy
  refine ((Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => hA i j).const_mul _).sub
    ((Finset.measurable_sum _ fun i _ => hB i).const_mul _) |>.add ((hC.comp measurable_fst).const_mul _)

theorem s94_quad_measurable {h : ℝ → Euc d → Euc d → ℝ}
    (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : Measurable fun q : ℝ≥0 × Ω => X q.1 q.2) :
    Measurable fun q : ℝ × Ω => r2QuadFluct μ h P X q.1 q.2 := by
  have hq : Measurable fun q : ℝ × Ω => (q.1.toNNReal, q.2) :=
    (measurable_fst.real_toNNReal).prodMk measurable_snd
  have hXq : Measurable fun q : ℝ × Ω => X q.1.toNNReal q.2 := hX.comp hq
  have hG : Measurable fun q : ℝ × Ω => pairEnergy (h q.1) (X q.1.toNNReal q.2) μ :=
    Measurable.comp (g := fun p : ℝ × EucConfig d N => pairEnergy (h p.1) p.2 μ)
      (f := fun q : ℝ × Ω => (q.1, X q.1.toNNReal q.2))
      (s94_pairEnergy_measurable (N := N) (μ := μ) hmeas) (measurable_fst.prodMk hXq)
  have hI : Measurable fun t : ℝ => ∫ ζ', pairEnergy (h t) (X t.toNNReal ζ') μ ∂P :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  unfold r2QuadFluct
  exact (hG.sub (hI.comp measurable_fst)).const_mul _

theorem s94_empFluct_measurable {a : Euc d → ℝ} (ha : IsR2Test a) {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → EucConfig d N) (hX : Measurable fun q : ℝ≥0 × Ω => X q.1 q.2) :
    Measurable fun q : ℝ × Ω => r2EmpFluct μ a X q.2 q.1 := by
  unfold r2EmpFluct
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
    exact measurable_const
  · simp_rw [Whole.pair_empirical hN]
    refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).sub
      measurable_const)
    have hq : Measurable fun q : ℝ × Ω => (q.1.toNNReal, q.2) :=
      (measurable_fst.real_toNNReal).prodMk measurable_snd
    exact (s94_test_continuous ha).measurable.comp ((measurable_pi_apply i).comp (hX.comp hq))

end Meas

end HRS.MS.R2Chaos
