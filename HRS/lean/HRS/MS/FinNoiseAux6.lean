import HRS.MS.FinNoiseAux5

/-!
# S8.6 `finite_noise`, packet P1e (S86): the particle integrand is Hilbert-Schmidt on every finite horizon

`s86_hs_all_horizons`: for a jointly Borel, bounded feature family `Γ` and progressive particles `X`, the
integrand `Φ_r(i,a) = c • Γ_a(r, X_i(r))` is `IsHSIntegrand P ℱ T` for EVERY `T : ℝ` (the form needed by
`HRS.hilbert_polar_coupling`).  Statement adopted from the Pro packet S8.6.04, checked: true.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

theorem s86_hs_all_horizons (d N : ℕ) (m H β B : ℝ) (hB : 0 ≤ B)
    (Γ : Fin d → ℝ → Euc d → KSpace d m H)
    (hΓ : ∀ i, Measurable (fun p : ℝ × Euc d => Γ i p.1 p.2))
    (hΓbound : ∀ (i : Fin d) (r : ℝ) (x : Euc d), ‖Γ i r x‖ ≤ B)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : ∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i)) :
    ∀ T : ℝ, IsHSIntegrand P ℱ T
      (fun r z (ia : Fin N × Fin d) =>
        Real.sqrt (2 / (N * β)) • Γ ia.2 r (X (Real.toNNReal r) z ia.1)) := by
  intro T
  set c : ℝ := Real.sqrt (2 / (N * β)) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  refine ⟨fun k => ?_, fun r z => Summable.of_finite, ?_⟩
  · intro τ
    have h1 := hX k.1 τ
    have h2 : Measurable[Subtype.instMeasurableSpace.prod (ℱ τ)]
        (fun p : Set.Iic τ × Ω => (p.1.1, X (Real.toNNReal p.1.1) p.2 k.1)) :=
      Measurable.prodMk (measurable_subtype_coe.comp measurable_fst) h1
    exact ((hΓ k.2).comp h2).const_smul c
  · have hpt : ∀ (r : ℝ) (z : Ω) (k : Fin N × Fin d), ‖(c • Γ k.2 r (X (Real.toNNReal r) z k.1))‖ₑ ^ 2 ≤
        ENNReal.ofReal ((c * B) ^ 2) := by
      intro r z k
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_smul, Real.norm_of_nonneg hc0]
      exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left (hΓbound _ _ _) hc0) 2
    unfold hsSqIntegralOn
    calc ∫⁻ w, (∫⁻ r in Icc 0 T, ∑' k : Fin N × Fin d,
          ‖(c • Γ k.2 r (X (Real.toNNReal r) w k.1))‖ₑ ^ 2) ∂P
        ≤ ∫⁻ w, (∫⁻ r in Icc 0 T, ((N * d : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((c * B) ^ 2)) ∂P := by
          refine lintegral_mono fun w => lintegral_mono fun r => ?_
          rw [tsum_fintype]
          calc ∑ k : Fin N × Fin d, ‖(c • Γ k.2 r (X (Real.toNNReal r) w k.1))‖ₑ ^ 2
              ≤ ∑ _k : Fin N × Fin d, ENNReal.ofReal ((c * B) ^ 2) :=
                Finset.sum_le_sum fun k _ => hpt r w k
            _ = _ := by simp
      _ < ⊤ := by
          simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
            measure_univ, mul_one]
          have hN : (((N * d : ℕ)) : ℝ≥0∞) < ⊤ := lt_top_iff_ne_top.2 (ENNReal.natCast_ne_top _)
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top hN ENNReal.ofReal_lt_top) ?_
          exact lt_of_le_of_lt (le_of_eq rfl) (by simp [Real.volume_Icc])

end HRS.MS.FinNoise
