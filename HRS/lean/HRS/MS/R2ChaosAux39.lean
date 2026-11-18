import HRS.MS.R2ChaosAux38

/-!
# HRS.MS.R2ChaosAux39 -- (a) part 1: tests separate `L²(μ)`; hyperplanes are `μ`-null

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

* `s94_test_separates`: if `f ∈ L²(ρ dx)` has `∫ f b dμ = 0` for every `b ∈ C_c^∞`, then `f = 0` `μ`-a.e.
  (fundamental lemma of the calculus of variations for `fρ ∈ L¹_loc(dx)`).
* `s94_hyperplane_null`: `{x | x i = r}` is Lebesgue-null.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_test_separates {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {f : Euc d → ℝ}
    (hf : MemLp f 2 (Whole.withDensityReal ρ))
    (h : ∀ b : Euc d → ℝ, IsR2Test b → ∫ x, f x * b x ∂(Whole.withDensityReal ρ) = 0) :
    f =ᵐ[Whole.withDensityReal ρ] 0 := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ
  have hρm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp hρ.measurable
  have hlt : ∀ᵐ x ∂(volume : Measure (Euc d)), ENNReal.ofReal (ρ x) < ⊤ := ae_of_all _ fun x => ENNReal.ofReal_lt_top
  have hint : Integrable f (Whole.withDensityReal ρ) := hf.integrable one_le_two
  have hint' : Integrable (fun x => ρ x • f x) (volume : Measure (Euc d)) := by
    have := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Euc d))) hρm hlt
      (g := f)).1 hint
    refine this.congr (ae_of_all _ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := (volume : Measure (Euc d)))
    (f := fun x => ρ x • f x) hint'.locallyIntegrable (fun b hb hbc => by
      have h1 := h b ⟨hb, hbc⟩
      have h2 : ∫ x, f x * b x ∂(Whole.withDensityReal ρ) = ∫ x, ρ x • (f x * b x) ∂(volume : Measure (Euc d)) := by
        unfold Whole.withDensityReal
        rw [integral_withDensity_eq_integral_toReal_smul hρm hlt]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
      rw [← h1, h2]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [smul_eq_mul]
      ring)
  unfold Whole.withDensityReal
  rw [Filter.EventuallyEq, ae_withDensity_iff hρm]
  filter_upwards [hz] with x hx hne
  have hpos : ρ x ≠ 0 := by
    intro h0; apply hne; simp [h0]
  simpa [hpos] using hx

theorem s94_hyperplane_null (i : Fin d) (r : ℝ) :
    (volume : Measure (Euc d)) {x : Euc d | x i = r} = 0 := by
  let ℓ : Euc d →ₗ[ℝ] ℝ := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).toLinearMap
  have hne : LinearMap.ker ℓ ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single i (1 : ℝ) ∈ LinearMap.ker ℓ := h ▸ Submodule.mem_top
    simp [ℓ] at this
  have h0 := Measure.addHaar_submodule (volume : Measure (Euc d)) (LinearMap.ker ℓ) hne
  have e : {x : Euc d | x i = r} = (fun x => x + (-r) • EuclideanSpace.single i (1 : ℝ)) ⁻¹'
      (LinearMap.ker ℓ : Set (Euc d)) := by
    ext x
    simp only [ℓ, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker]
    simp
    constructor <;> intro h <;> linarith
  rw [e, measure_preimage_add_right]
  exact h0

end HRS.MS.R2Chaos
