import HRS.ME.UIPath
import HRS.ME.UIFinal

/-!
# Q1: the shifted-window finite-dimensional clause (`shifted_smoothDist_tendsto`)

Copy of the second clause of `HRS.ME.Ret.ui_qualitative_of_comparison_proof` (`HRS/ME/RetQual.lean`), without the
Gaussian vectors `G`, which that clause does not use.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

theorem shifted_smoothDist_tendsto (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (T : ℝ) (hT : 0 ≤ T) (p : ℕ) (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (S : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → S.IsSolutionOn (PDE.mfData d s hs0 hsd V β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (S.mΩ n))
      (W' : ℝ≥0 → S.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (S.P n) ℱ W' (S.W n) (S.X n))
    (hν : ∀ n, (S.P n).map (S.X₀ n) ≪ canonicalGibbs (periodicRiesz d s) V (n + 2) β)
    (hUI : Tendsto (uiTail d s β V (fun n => (S.P n).map (S.X₀ n))) atTop (𝓝 0))
    (t : Fin p → ℝ) (ht : ∀ a, t a ∈ Set.Icc (0 : ℝ) T)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => smoothDist 2
        (law (S.P n) fun ω => (WithLp.toLp 2 fun a =>
          linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) (φ a)
            (S.X n (u n + t a).toNNReal ω) : EuclideanSpace ℝ (Fin p)))
        (ProbabilityTheory.multivariateGaussian 0
          (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ t φ))) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hc0, hcmp⟩ := HRS.ME.Ret.ui_comparison_proof (d := d) hd hs0 hsd hβ V hV ρβ hρβ hρS
    hρpos T hT p φ hφ
  have hδ : Tendsto (fun n : ℕ => deltaN d s (n + 2)) atTop (𝓝 0) :=
    (HRS.External.RefMarg.tendsto_deltaN hd hs0 hsd).comp (tendsto_add_atTop_nat 2)
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (deltaN d s (n + 2))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hδ
    rw [Real.sqrt_zero] at h
    exact h
  have hexp : Tendsto (fun n : ℕ => Real.exp (-c * u n)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hu.const_mul_atTop hc0)
    refine Tendsto.congr (fun n => ?_) h
    simp [Function.comp_apply, neg_mul]
  have hL : ∀ η : ℝ, 0 < η → ∃ L : ℝ, 1 ≤ L ∧
      HRS.uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L ≤ 1 / 2 ∧
      4 * HRS.uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L ≤ ENNReal.ofReal η := by
    intro η hη
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (η / 4) := ENNReal.ofReal_pos.2 (by linarith)
    have hev : ∀ᶠ L in atTop,
        (HRS.uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L ≤ 1 / 2 ∧
          HRS.uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L ≤ ENNReal.ofReal (η / 4)) ∧
        1 ≤ L :=
      ((ENNReal.tendsto_nhds_zero.1 hUI (1 / 2) (by norm_num)).and
        (ENNReal.tendsto_nhds_zero.1 hUI _ hpos)).and (eventually_ge_atTop 1)
    obtain ⟨L, ⟨hL2, hL3⟩, hL1⟩ := hev.exists
    refine ⟨L, hL1, hL2, ?_⟩
    calc 4 * HRS.uiTail d s β V (fun n => (S.P n).map (S.X₀ n)) L
        ≤ 4 * ENNReal.ofReal (η / 4) := by gcongr
      _ = ENNReal.ofReal η := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (p := 4) (by norm_num)]
        congr 1
        ring
  have hconv : ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) → (∀ ε > 0, ∀ᶠ n in atTop, f n < ε) →
      Tendsto f atTop (𝓝 0) := by
    intro f hf hlim
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hlim ε hε] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
    exact hn
  have hgen : ∀ (x a η : ℝ) (b : ℝ≥0∞), 0 ≤ a → 0 ≤ η →
      ENNReal.ofReal x ≤ ENNReal.ofReal a + 4 * b → 4 * b ≤ ENNReal.ofReal η → x ≤ a + η := by
    intro x a η b ha hη hx hb
    have hq : 0 ≤ a + η := by linarith
    have h2 : ENNReal.ofReal x ≤ ENNReal.ofReal (a + η) := by
      rw [ENNReal.ofReal_add ha hη]
      exact hx.trans (by gcongr)
    exact (ENNReal.ofReal_le_ofReal_iff hq).1 h2
  apply hconv
  · intro n
    exact smoothDist_nonneg _ _ _
  · intro ε hε
    obtain ⟨L, hL1, hL2, hL3⟩ := hL (ε / 2) (half_pos hε)
    have hYL : Tendsto (fun n : ℕ =>
        C * Real.sqrt L * (Real.sqrt (deltaN d s (n + 2)) + Real.exp (-c * u n))) atTop (𝓝 0) := by
      have h := (hsq.add hexp).const_mul (C * Real.sqrt L)
      rw [zero_add, mul_zero] at h
      exact h
    filter_upwards [hYL.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))] with n hn
    have hA := (hcmp S hS hSF hν L hL1 hL2 n).2 (u n) (hu0 n) t ht
    have hB := hgen _ _ _ _
      (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg L))
        (add_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le))
      (half_pos hε).le hA hL3
    linarith

end HRS.ME.UIPathShifted

end
