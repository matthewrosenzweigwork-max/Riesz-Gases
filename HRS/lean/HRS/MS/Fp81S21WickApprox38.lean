import HRS.MS.Fp81S21WickApprox33
import HRS.MS.Fp81S21GaussTimeRep3

/-! Fixed linear and quadratic physical Gaussian selectors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The canonical linear and physical quadratic selectors, with their
separately fixed moment constants and without identifying their coefficients. -/
structure fp81s21_GaussianPhysical31 (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (εG εB : ℕ → ℝ) where
  MηG : ℝ
  MηG_nonneg : 0 ≤ MηG
  qsηG : (G : GaussianRealization R) → ℝ → G.Ω → r26t6_Coeff
  gaussian_linear : ∀ G, fp81s21_gaussian_canonical_time_payload p Es E G.P
    (fun u ω f => OscDual.eval (G.Z u ω) f) MηG (qsηG G)
    (fp81s21_gaussian_embedFamily p Es E (qsηG G)) εG
  quadratic : fp81s21_QuadraticPhysical31 p R Es E εB

/-- Select the complete linear and quadratic Gaussian payloads before
approximation orders, horizons, shifts, and realizations are varied. -/
theorem fp81s21_gaussianPhysical31_exists (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ εG εB : ℕ → ℝ,
    (∀ m, 0 ≤ εG m) ∧ Tendsto εG atTop (𝓝 0) ∧
    (∀ m, 0 ≤ εB m) ∧ Tendsto εB atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      Nonempty (fp81s21_GaussianPhysical31 p R Es E εG εB) := by
  let g := Classical.choice (fp81s21_gaussian_canonical_TimeRep_tails p Es E)
  obtain ⟨εB, hεB, hεBlim, δB, hδB, hδBh, hb⟩ :=
    fp81s21_quadraticPhysical31_exists p Es E
  let δ0 := min g.delta₀ δB
  refine ⟨g.epsilon, εB, g.epsilon_nonneg, g.epsilon_tendsto, hεB, hεBlim,
    δ0, lt_min g.delta₀_positive hδB, (min_le_left _ _).trans g.delta₀_half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨MG, hMG, hg⟩ := g.realizations δ hδ (hδle.trans (min_le_left _ _)) R
  have hB := hb δ hδ (hδle.trans (min_le_right _ _)) R
  choose qs hqs using hg
  exact ⟨⟨MG, hMG, qs, hqs, Classical.choice hB⟩⟩

#print axioms fp81s21_GaussianPhysical31
#print axioms fp81s21_gaussianPhysical31_exists
end HRS.Fp81.S21
end
