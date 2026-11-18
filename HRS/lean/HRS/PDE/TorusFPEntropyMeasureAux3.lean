import HRS.PDE.TorusFPEntropyMeasureAux2

/-!
# D3-b, Aux3: finiteness of classical entropies, the real "liminf" combination lemma, continuity pieces

Helpers `d3b_*`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- The relative entropy of a continuous positive density is finite. -/
theorem d3b_klDiv_classical_ne_top {P : Measure (Torus n)} [IsProbabilityMeasure P] {w : Torus n → ℝ}
    (hc : Continuous w) (hpos : ∀ x, 0 < w x) :
    relEntropy (P.withDensity fun x => ENNReal.ofReal (w x)) P ≠ ⊤ := by
  haveI : IsFiniteMeasure (P.withDensity fun x => ENNReal.ofReal (w x)) :=
    isFiniteMeasure_withDensity_ofReal (d3a_hint P hc).hasFiniteIntegral
  have hac : (P.withDensity fun x => ENNReal.ofReal (w x)) ≪ P := withDensity_absolutelyContinuous P _
  have hmeas : Measurable fun x => ENNReal.ofReal (w x) := hc.measurable.ennreal_ofReal
  have hllr : llr (P.withDensity fun x => ENNReal.ofReal (w x)) P =ᵐ[P] fun x => Real.log (w x) := by
    filter_upwards [Measure.rnDeriv_withDensity P hmeas] with x hx
    simp only [llr, hx, ENNReal.toReal_ofReal (hpos x).le]
  unfold relEntropy
  refine InformationTheory.klDiv_ne_top hac ?_
  exact (d3a_hint _ (hc.log fun x => (hpos x).ne')).congr (hac.ae_eq hllr).symm

/-- Combination of two `liminf` bounds with an asymptotic upper bound for the sum. -/
theorem d3b_combine {κ : ℝ} (hκ : 0 < κ) {a j : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hj : ∀ k, 0 ≤ j k)
    {α β : ℝ≥0∞} (hα : α ≤ liminf (fun k => ENNReal.ofReal (a k)) atTop)
    (hβ : β ≤ liminf (fun k => ENNReal.ofReal (j k)) atTop) {R : ℝ}
    (hR : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a k + κ * j k ≤ R + ε) :
    α ≠ ⊤ ∧ β ≠ ⊤ ∧ α.toReal + κ * β.toReal ≤ R := by
  have h1 := hR 1 one_pos
  have hα1 : α ≤ ENNReal.ofReal (R + 1) := by
    refine hα.trans ?_
    calc liminf (fun k => ENNReal.ofReal (a k)) atTop ≤ liminf (fun _ : ℕ => ENNReal.ofReal (R + 1)) atTop :=
          liminf_le_liminf (h1.mono fun k hk => ENNReal.ofReal_le_ofReal (by nlinarith [ha k, hj k]))
      _ = _ := liminf_const _
  have hβ1 : β ≤ ENNReal.ofReal ((R + 1) / κ) := by
    refine hβ.trans ?_
    calc liminf (fun k => ENNReal.ofReal (j k)) atTop ≤
          liminf (fun _ : ℕ => ENNReal.ofReal ((R + 1) / κ)) atTop :=
          liminf_le_liminf (h1.mono fun k hk => ENNReal.ofReal_le_ofReal (by
            rw [le_div_iff₀ hκ]; nlinarith [ha k, hj k]))
      _ = _ := liminf_const _
  have hαt : α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hα1
  have hβt : β ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hβ1
  refine ⟨hαt, hβt, ?_⟩
  have key : ∀ (γ : ℝ≥0∞) (u : ℕ → ℝ), (∀ k, 0 ≤ u k) → γ ≠ ⊤ →
      γ ≤ liminf (fun k => ENNReal.ofReal (u k)) atTop → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, γ.toReal - ε ≤ u k := by
    intro γ u hu hγ hle ε hε
    by_cases h0 : γ.toReal - ε ≤ 0
    · exact Eventually.of_forall fun k => h0.trans (hu k)
    · push_neg at h0
      have hlt : ENNReal.ofReal (γ.toReal - ε) < liminf (fun k => ENNReal.ofReal (u k)) atTop := by
        refine lt_of_lt_of_le ?_ hle
        calc ENNReal.ofReal (γ.toReal - ε) < ENNReal.ofReal γ.toReal :=
              (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
          _ = γ := ENNReal.ofReal_toReal hγ
      filter_upwards [eventually_lt_of_lt_liminf hlt] with k hk
      exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 hk).1.le
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / (2 + κ) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨k, hk⟩ := ((key α a ha hαt hα ε hε).and
    ((key β j hj hβt hβ ε hε).and (hR ε hε))).exists
  obtain ⟨hk1, hk2, hk3⟩ := hk
  have : ε * (2 + κ) = δ := by rw [hεdef]; field_simp
  nlinarith

end HRS
