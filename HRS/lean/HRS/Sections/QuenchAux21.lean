import HRS.Sections.QuenchAux20

/-!
# Packet QUENCH (Q27), part 21: domination of the window supremum

If the coordinates of `W(t)` are dominated (uniformly in `t ∈ [0,T]`) by measurable `B_j` with
`∑_j E B_j² < ∞`, then `sup_t ‖W(t)‖²` is dominated by an integrable `H`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

variable {d : ℕ} {m T : ℝ}

section Dom

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma ofReal_norm_sq_eq_tsum (x : NegSobolev d m) :
    ENNReal.ofReal (‖x‖ ^ 2) = ∑' j : NonzeroLattice d, ‖NegSobolev.coord x j‖ₑ ^ 2 := by
  obtain ⟨h1, h2⟩ := NegSobolev.coord_sq x
  rw [h2, ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) h1]
  refine tsum_congr fun j => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem winData_dom {Wt : ℝ → Ω → NegSobolev d m} (hmeas : ∀ t, Measurable (Wt t))
    (B : NonzeroLattice d → Ω → ℝ≥0∞) (hBm : ∀ j, AEMeasurable (B j) P)
    (hB : ∀ᵐ ω ∂P, ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖NegSobolev.coord (Wt t ω) j‖ₑ ≤ B j ω)
    (hsum : ∑' j, ∫⁻ ω, (B j ω) ^ 2 ∂P ≠ ⊤) :
    ∃ H : Ω → ℝ, Integrable H P ∧ ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Wt t ω‖ ^ 2 ≤ H ω := by
  set Hₑ : Ω → ℝ≥0∞ := fun ω => ∑' j, (B j ω) ^ 2 with hHe
  have hHm : AEMeasurable Hₑ P := AEMeasurable.ennreal_tsum fun j => (hBm j).pow_const 2
  have hint : ∫⁻ ω, Hₑ ω ∂P ≠ ⊤ := by
    simp only [hHe]
    rw [lintegral_tsum fun j => ((hBm j).pow_const 2)]
    exact hsum
  refine ⟨fun ω => (Hₑ ω).toReal, integrable_toReal_of_lintegral_ne_top hHm hint, ?_⟩
  have hlt : ∀ᵐ ω ∂P, Hₑ ω < ⊤ := ae_lt_top' hHm hint
  filter_upwards [hB, hlt] with ω h1 h2 t ht
  have h3 : ENNReal.ofReal (‖Wt t ω‖ ^ 2) ≤ Hₑ ω := by
    rw [ofReal_norm_sq_eq_tsum]
    exact ENNReal.tsum_le_tsum fun j => by gcongr; exact h1 j t ht
  exact (ENNReal.ofReal_le_iff_le_toReal h2.ne).1 h3

end Dom

end Qch

end HRS
