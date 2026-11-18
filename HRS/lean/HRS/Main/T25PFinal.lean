import HRS.Main.T25PAux33
import HRS.Main.T25Final

/-!
# T25P: relocated proofs of `prepared_fluctuations` and `prepared_fluctuations_W2` (Theorem 2.5)

RELOCATION PATTERN: the frozen statements of `HRS/Main/Headline.lean` are not edited; each is restated VERBATIM here as
`<name>_proof` and tied by `example := (@<name>_proof : type_of% @HRS.Main.<name>)`.

Proof chain (all in `HRS.T25P`, files `T25PAux1-33`): coupling + first enlargement (`t25p_enlarge_coupled`), window-law
identification (`t25p_hid`), core estimate (`t25p_core_gen`), `L^1`/`L^2` bounds for `Ψ_a` and the trace discrepancy,
clause 1 = `t25p_clause1`, clause 3 = `t25p_clause3` (re-basing `t25p_rebase`, uniqueness `t25p_lin_unique`), `W₂` = `t25p_W2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Theorem 2.5 (`H:thm:prepared`), smooth, `W₁` and `E_m`-initial-term bounds. -/
theorem prepared_fluctuations_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        (S.initW m 1 P X₀ ν ≠ ⊤ →
          smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            C * (Real.exp (-c * a) * (S.initW m 1 P X₀ ν).toReal +
              S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N)) ∧
          wassersteinE 1 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) * (S.initW m 1 P X₀ ν).toReal +
              S.B N (law P X₀) / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4)))) ∧
        smoothDist 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
          C * (smoothDist 2 (law P (fun ω => etaE m (X₀ ω) S.μ0)) ν +
            S.B N (law P X₀) / Real.sqrt N + Real.sqrt (S.B N (law P X₀) / N)) := by
  obtain ⟨C1, c1, hC1, hc1, h1⟩ := HRS.T25P.t25p_clause1 S m hm T hT
  obtain ⟨C3, hC3, h3⟩ := HRS.T25P.t25p_clause3 S m hm T hT
  refine ⟨max C1 C3, c1, lt_max_of_lt_left hC1, hc1, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hrel ν Ω' _ P' _ Y₀ Y hY
  have hB0 : 0 ≤ S.B N (law P X₀) := HRS.T25P.t25p_B_nonneg S hN (law P X₀)
  have hsN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hf0 : 0 ≤ S.B N (law P X₀) / Real.sqrt N := div_nonneg hB0 hsN
  have hg0 : 0 ≤ Real.sqrt (S.B N (law P X₀) / N) := Real.sqrt_nonneg _
  have hh0 : 0 ≤ (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (div_nonneg hB0 (Nat.cast_nonneg N)) _
  refine ⟨fun hfin => ?_, ?_⟩
  · obtain ⟨hs, hw⟩ := h1 a ha N hN P X₀ W X hSel hfilt hrel ν P' Y₀ Y hY hfin
    have hx0 : 0 ≤ Real.exp (-c1 * a) * (S.initW m 1 P X₀ ν).toReal :=
      mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
    refine ⟨hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
      hw.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))⟩
  · exact (h3 a ha N hN P X₀ W X hSel hfilt hrel ν P' Y₀ Y hY).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (add_nonneg (add_nonneg (smoothDist_nonneg 2 _ _) hf0) hg0))

/-- Theorem 2.5, the `W₂` bound. -/
theorem prepared_fluctuations_W2_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (p₀ : ℝ) (hp₀ : 1 < p₀) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        relEntropy (law P X₀) (S.refMeasure N 0) < ⊤ →
        MemLp (fun Y => (((law P X₀).rnDeriv (S.refMeasure N 0)) Y).toReal) (ENNReal.ofReal p₀)
          (S.refMeasure N 0) →
      ∀ (ν : Measure (NegSobolev d m)) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
        [IsProbabilityMeasure P'] (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
        S.initW m 2 P X₀ ν ≠ ⊤ →
          wassersteinE 2 (S.etaLaw m T a P X) (law P' (windowPath m T a Y)) ≤
            ENNReal.ofReal (C * (Real.exp (-c * a) * (S.initW m 2 P X₀ ν).toReal +
              S.J N (law P X₀) p₀ / Real.sqrt N +
              (S.B N (law P X₀) / N) ^ ((1 : ℝ) / 4))) :=
  HRS.T25P.t25p_W2 S m hm T hT p₀ hp₀

example := (@prepared_fluctuations_proof : type_of% @HRS.Main.prepared_fluctuations)

example := (@prepared_fluctuations_W2_proof : type_of% @HRS.Main.prepared_fluctuations_W2)

end Main

end HRS

end
