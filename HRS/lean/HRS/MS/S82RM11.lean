import HRS.MS.S82RM10

/-!
# S8.2 R02 (S82R), M11: iterated weights (admissibility, decay, constants)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- The iterated weights `W^{(J)} = S^J W`. -/
def s82r_wseq (μ : Measure E) (Γ : E → E → ℝ) (n : ℕ) (W : Fin n → E → ℝ) (J : ℕ) :
    Fin n → E → ℝ := (s82r_Sw μ Γ n)^[J] W

lemma s82r_wseq_succ (μ : Measure E) (Γ : E → E → ℝ) (n : ℕ) (W : Fin n → E → ℝ) (J : ℕ) :
    s82r_wseq μ Γ n W (J + 1) = s82r_Sw μ Γ n (s82r_wseq μ Γ n W J) := by
  unfold s82r_wseq; rw [Function.iterate_succ_apply']

lemma s82r_wseq_zero (μ : Measure E) (Γ : E → E → ℝ) (n : ℕ) (W : Fin n → E → ℝ) :
    s82r_wseq μ Γ n W 0 = W := rfl

lemma s82r_wseq_ok [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {θ : ℝ}
    (hθ : ∀ u, ∫ z, Γ z u ∂μ ≤ θ) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) (J : ℕ) : s82r_WOK (s82r_wseq μ Γ n W J) := by
  induction J with
  | zero => exact hW
  | succ J ih =>
      rw [s82r_wseq_succ]
      exact s82r_Sw_ok hΓ hΓ0 hθ hG0 ih

/-- Geometric decay of the sup-norm budget. -/
lemma s82r_wseq_decay [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {Γ : E → E → ℝ}
    (hΓ : Measurable (uncurry Γ)) (hΓ0 : ∀ z u, 0 ≤ Γ z u) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ u, ∫ z, Γ z u ∂μ ≤ θ) {G0 : ℝ} (hG0 : ∀ z u, Γ z u ≤ G0)
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) {B : Fin n → ℝ} (hB0 : ∀ ℓ, 0 ≤ B ℓ)
    (hB : ∀ ℓ z, W ℓ z ≤ B ℓ) (J : ℕ) :
    ∃ B' : Fin n → ℝ, (∀ ℓ, 0 ≤ B' ℓ) ∧ (∀ ℓ z, s82r_wseq μ Γ n W J ℓ z ≤ B' ℓ) ∧
      ∑ ℓ, B' ℓ ≤ (1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ) ^ J * ∑ ℓ, B ℓ := by
  induction J with
  | zero => exact ⟨B, hB0, hB, by simp⟩
  | succ J ih =>
      obtain ⟨B', hB'0, hB', hsum⟩ := ih
      obtain ⟨B'', h0, h1, h2⟩ := s82r_Sw_decay hΓ hΓ0 hθ0 hθ hG0
        (s82r_wseq_ok hΓ hΓ0 hθ hG0 hW J) hB'0 hB'
      refine ⟨B'', h0, fun ℓ z => ?_, ?_⟩
      · rw [s82r_wseq_succ]; exact h1 ℓ z
      · have hr0 : 0 ≤ 1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ := by
          have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
          have : 0 ≤ 1 - 1 / (n : ℝ) := by rw [sub_nonneg, div_le_one (by linarith)]; exact hn
          have h3 : 0 ≤ ((n : ℝ) - 1) / n * θ := mul_nonneg (div_nonneg (by linarith) (by linarith)) hθ0
          linarith
        calc ∑ ℓ, B'' ℓ ≤ (1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ) * ∑ ℓ, B' ℓ := h2
          _ ≤ (1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ) *
              ((1 - 1 / (n : ℝ) + (((n : ℝ) - 1) / n) * θ) ^ J * ∑ ℓ, B ℓ) :=
            mul_le_mul_of_nonneg_left hsum hr0
          _ = _ := by ring

end HRS.MS.S82R

end
