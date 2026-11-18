import HRS.MS.SA16Y8Br1

/-!
# S.A.16 (SA16Y8) Jc1: joint continuity from continuity in `τ` at fixed `x` and equicontinuity in `x` (classical clause, K4, part 3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA

section Jc1
variable {d : ℕ}

/-- `h(τ,x)` is jointly continuous on `S × ℝ^d` if `τ ↦ h τ x₀` is continuous on `S` for each `x₀` and `x ↦ h τ x` is equicontinuous
(uniformly in `τ ∈ S`). -/
theorem sa16y8_jc {E : Type*} [PseudoMetricSpace E] (S : Set ℝ) (h : ℝ → Euc d → E)
    (hτ : ∀ x₀, ContinuousOn (fun τ => h τ x₀) S)
    (hx : ∀ (x₀ : Euc d) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ S, ∀ x : Euc d, dist x x₀ < δ →
      dist (h τ x) (h τ x₀) < ε) :
    ContinuousOn (fun q : ℝ × Euc d => h q.1 q.2) (S ×ˢ univ) := by
  rintro ⟨τ₀, x₀⟩ hq
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, h1⟩ := hx x₀ (ε / 2) (by linarith)
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuousWithinAt_iff.1 (hτ x₀ τ₀ hq.1) (ε / 2) (by linarith)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  rintro ⟨τ, x⟩ hτx hdist
  have hτS : τ ∈ S := hτx.1
  have hd1 : dist x x₀ < δ1 := by
    have : dist (τ, x) (τ₀, x₀) < min δ1 δ2 := hdist
    rw [Prod.dist_eq] at this
    exact lt_of_le_of_lt (le_max_right _ _) (this.trans_le (min_le_left _ _))
  have hd2 : dist τ τ₀ < δ2 := by
    have : dist (τ, x) (τ₀, x₀) < min δ1 δ2 := hdist
    rw [Prod.dist_eq] at this
    exact lt_of_le_of_lt (le_max_left _ _) (this.trans_le (min_le_right _ _))
  calc dist (h τ x) (h τ₀ x₀) ≤ dist (h τ x) (h τ x₀) + dist (h τ x₀) (h τ₀ x₀) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (h1 τ hτS x hd1) (h2 hτS hd2)
    _ = ε := by ring

/-- transport of the two hypotheses by a continuous linear map -/
theorem sa16y8_transport {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : G →L[ℝ] E) (S : Set ℝ) (g : ℝ → Euc d → G)
    (hτ : ∀ x₀, ContinuousOn (fun τ => g τ x₀) S)
    (hx : ∀ (x₀ : Euc d) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ S, ∀ x : Euc d, dist x x₀ < δ →
      dist (g τ x) (g τ x₀) < ε) :
    (∀ x₀, ContinuousOn (fun τ => L (g τ x₀)) S) ∧
    (∀ (x₀ : Euc d) (ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ S, ∀ x : Euc d, dist x x₀ < δ →
      dist (L (g τ x)) (L (g τ x₀)) < ε) := by
  refine ⟨fun x₀ => L.continuous.comp_continuousOn (hτ x₀), fun x₀ ε hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hx x₀ (ε / (‖L‖ + 1)) (by positivity)
  refine ⟨δ, hδ, fun τ hτ x hxd => ?_⟩
  have h1 := h τ hτ x hxd
  rw [dist_eq_norm] at h1 ⊢
  rw [← map_sub]
  calc ‖L (g τ x - g τ x₀)‖ ≤ ‖L‖ * ‖g τ x - g τ x₀‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (ε / (‖L‖ + 1)) := mul_le_mul_of_nonneg_left h1.le (norm_nonneg _)
    _ < ε := by
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith [norm_nonneg L]

end Jc1

end HRS.Whole.AppendixA.Phase2SA16Q
