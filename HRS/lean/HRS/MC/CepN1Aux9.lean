import HRS.MC.CepN1Aux8
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Packet CEPN1, part 9: Lipschitz approximation of a continuous function on `[0,T']`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set Polynomial
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

theorem cepn1_lip_approx {f : ℝ → ℝ} (hf : Continuous f) (hf0 : f 0 = 0) {T' δ : ℝ} (hT' : 0 < T')
    (hδ : 0 < δ) :
    ∃ (g : ℝ≥0 → ℝ) (L : ℝ), 0 ≤ L ∧ g 0 = 0 ∧ (∀ s t : ℝ≥0, |g s - g t| ≤ L * |(s : ℝ) - t|) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ T' → |g t - f t| < δ := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 T' f hf.continuousOn (δ / 2) (by positivity)
  have hcd : ContDiff ℝ 1 (fun x : ℝ => p.eval x) := by
    have := Polynomial.contDiff_aeval (𝕜 := ℝ) p 1
    simpa using this
  obtain ⟨K, hK⟩ := hcd.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := T'))
  set g0 : ℝ≥0 → ℝ := fun t => p.eval (min (t : ℝ) T') with hg0
  have hg0L : ∀ s t : ℝ≥0, |g0 s - g0 t| ≤ K * |(s : ℝ) - t| := by
    intro s t
    have hmem : ∀ u : ℝ≥0, min (u : ℝ) T' ∈ Set.Icc (0 : ℝ) T' := fun u =>
      ⟨le_min u.2 hT'.le, min_le_right _ _⟩
    have h1 := hK.dist_le_mul _ (hmem s) _ (hmem t)
    rw [Real.dist_eq, Real.dist_eq] at h1
    have h2 : |min (s : ℝ) T' - min (t : ℝ) T'| ≤ |(s : ℝ) - t| := by
      have := abs_min_sub_min_le_max (s : ℝ) T' (t : ℝ) T'
      simpa using this
    calc |g0 s - g0 t| ≤ K * |min (s : ℝ) T' - min (t : ℝ) T'| := h1
      _ ≤ K * |(s : ℝ) - t| := by gcongr
  refine ⟨fun t => g0 t - g0 0, K, K.2, by simp, ?_, ?_⟩
  · intro s t
    simpa using hg0L s t
  · intro t ht
    have h0 : |g0 0 - f 0| < δ / 2 := by
      have := hp 0 ⟨le_rfl, hT'.le⟩
      have e : min (0 : ℝ) T' = 0 := min_eq_left hT'.le
      simpa [hg0, e] using this
    have h1 : |g0 t - f t| < δ / 2 := by
      have := hp (t : ℝ) ⟨t.2, ht⟩
      have e : min (t : ℝ) T' = t := min_eq_left ht
      simpa [hg0, e] using this
    rw [hf0] at h0
    calc |g0 t - g0 0 - f t| = |(g0 t - f t) - g0 0| := by ring_nf
      _ ≤ |g0 t - f t| + |g0 0| := abs_sub _ _
      _ < δ := by
        have : |g0 0| < δ / 2 := by simpa using h0
        linarith

end HRS.MC.CepN1
