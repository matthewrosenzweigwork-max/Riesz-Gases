import HRS.MS.SuppA0Aux2

/-!
# A0: S6.8 `mov_translation` (all four clauses), clause (2) under the approved hypothesis `IsRegularMFRd`

Clause (2) is proved from the time-dependent weak form `HRS.MH.mf_time_dependent_proof` applied to the shifted test
functions `f r x = ψ(x + a_r)`, `ft r x = ⟨∇ψ(x + a_r), -q a_r⟩`, followed by the change of variables `x ↦ x + a_r`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.A0

open HRS.Whole HRS.MH.DualityRd HRS.Whole.AppendixA

variable {d : ℕ}

lemma a0_isProb_shift {ρ : Euc d → ℝ} (h : Whole.IsProbDensity ρ) (a : Euc d) :
    Whole.IsProbDensity (fun x => ρ (x - a)) :=
  ⟨fun x => h.nonneg _, h.measurable.comp (measurable_sub_const a),
    (integral_sub_right_eq_self ρ a).trans h.integral_one⟩

lemma a0_second_moment_shift {ρ : Euc d → ℝ} (h : Whole.IsProbDensity ρ)
    (h2 : Integrable (fun x => ‖x‖ ^ 2 * ρ x)) (a : Euc d) :
    Integrable (fun x => ‖x‖ ^ 2 * ρ (x - a)) := by
  have hρ : Integrable ρ := movtr_integrable_of_prob h
  have hI : Integrable (fun y => ‖y + a‖ ^ 2 * ρ y) := by
    refine Integrable.mono' ((h2.const_mul 2).add (hρ.const_mul (2 * ‖a‖ ^ 2))) ?_ ?_
    · exact ((continuous_norm.comp (continuous_id.add continuous_const)).pow 2).aestronglyMeasurable.mul
        h.measurable.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      have h0 := h.nonneg y
      rw [Real.norm_of_nonneg (by positivity)]
      have : ‖y + a‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖a‖ ^ 2 := by
        have h1 : ‖y + a‖ ^ 2 ≤ (‖y‖ + ‖a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le y a) 2
        nlinarith [sq_nonneg (‖y‖ - ‖a‖)]
      show ‖y + a‖ ^ 2 * ρ y ≤ 2 * (‖y‖ ^ 2 * ρ y) + 2 * ‖a‖ ^ 2 * ρ y
      nlinarith
  have := hI.comp_sub_right a
  simpa using this

theorem a0_clause2 {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (a₀ : Euc d)
    (T Λ : ℝ) (ρ : ℝ → Euc d → ℝ) (hreg : IsRegularMFRd s 3 Λ T ρ)
    (hsol : IsWholeMeanFieldSolution (quadraticGradientDyn d s q β) T ρ) :
    IsWholeMeanFieldSolution (quadraticGradientDyn d s q β) T
      (fun t x => ρ t (x - movShift q a₀ t)) := by
  obtain ⟨ΛV, hV⟩ := a0_vhyp (d := d) q
  have hMF : MFData s Λ T ΛV 0 (quadraticGradientDyn d s q β) ρ :=
    ⟨rfl, hs0, hsd, inv_nonneg.2 hβ.le, hV, hsol, hreg⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact a0_isProb_shift (hsol.density t ht) _
  · intro t ht
    exact a0_second_moment_shift (hsol.density t ht) (hsol.second_moment t ht) _
  · intro ψ hψ t ht
    have key := (mf_time_dependent_proof hMF ht (a0_isC12 hψ hq.le a₀ t) t ⟨ht.1, le_rfl⟩).2
    have hint : ∀ r ∈ Set.Icc (0 : ℝ) t,
        (Whole.pair (Whole.withDensityReal (fun x => ρ r (x - movShift q a₀ r)))
            (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian ψ x -
              inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient ψ x)) +
          interactionPairingW (quadraticGradientDyn d s q β) ψ
            (Whole.withDensityReal (fun x => ρ r (x - movShift q a₀ r)))
            (Whole.withDensityReal (fun x => ρ r (x - movShift q a₀ r)))) =
        (Whole.pair (Whole.withDensityReal (ρ r))
            (driftTestRd (quadraticGradientDyn d s q β) (a0_f ψ q a₀) (a0_ft ψ q a₀) r) +
          interactionPairingW (quadraticGradientDyn d s q β) (a0_f ψ q a₀ r)
            (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))) := by
      intro r _
      have hp : Whole.pair (Whole.withDensityReal (fun x => ρ r (x - movShift q a₀ r)))
            (fun x => (quadraticGradientDyn d s q β).invβ * Laplacian.laplacian ψ x -
              inner ℝ (gradient (quadraticGradientDyn d s q β).V x) (gradient ψ x)) =
          Whole.pair (Whole.withDensityReal (ρ r))
            (driftTestRd (quadraticGradientDyn d s q β) (a0_f ψ q a₀) (a0_ft ψ q a₀) r) := by
        rw [a0_pair_shift]
        congr 1
        funext y
        rw [a0_driftTest]
        rfl
      have hi : interactionPairingW (quadraticGradientDyn d s q β) ψ
            (Whole.withDensityReal (fun x => ρ r (x - movShift q a₀ r)))
            (Whole.withDensityReal (fun x => ρ r (x - movShift q a₀ r))) =
          interactionPairingW (quadraticGradientDyn d s q β) (a0_f ψ q a₀ r)
            (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r)) := by
        rw [← a0_map_withDensity]
        exact (a0_interaction_shift _ ψ _ _).symm
      rw [hp, hi]
    show Whole.pair (Whole.withDensityReal (fun x => ρ t (x - movShift q a₀ t))) ψ -
        Whole.pair (Whole.withDensityReal (fun x => ρ 0 (x - movShift q a₀ 0))) ψ = _
    rw [setIntegral_congr_fun measurableSet_Icc hint, a0_pair_shift, a0_pair_shift]
    exact sub_eq_iff_eq_add'.2 key

end HRS.MS.A0

namespace HRS.Whole

/-- S6.8 `mov_translation` with clause (2) proved under the approved hypothesis `IsRegularMFRd`; clauses (1), (3),
(4) are those of the frozen proof. -/
theorem mov_translation_proof : type_of% @HRS.Whole.mov_translation := by
  intro d s hd hs0 hsd β q hβ hq a₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N T Ω _ P Y₀ W Y h
    exact movtr_strong_translate P s q β T Y₀ W Y h a₀
  · intro T Λ ρ hreg hsol
    exact HRS.MS.A0.a0_clause2 hs0 hsd β q hβ hq a₀ T Λ ρ hreg hsol
  · intro N β₀ _ μ hμ
    exact movtr_modulatedGibbs_translate (rieszKernel d s) N β₀ μ a₀
  · intro N β₀ μ hμ
    exact ⟨fun X => movtr_modulatedEnergy_translate (rieszKernel d s) μ a₀ X,
      movtr_gibbsNormalizer_translate (rieszKernel d s) N β₀ μ a₀⟩

end HRS.Whole
