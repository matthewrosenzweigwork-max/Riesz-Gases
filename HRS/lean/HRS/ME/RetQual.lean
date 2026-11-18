import HRS.Sections.Sec5
import HRS.Equilibrium.ReferenceMarginal

/-!
# `ui_qualitative` from `ui_comparison`

The qualitative initial-law and shifted-window conclusions follow from the quantitative comparison
`ui_comparison` by letting `Θ(L) → 0` and `δ_N → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

theorem ui_qualitative_of_comparison_proof (d : ℕ) (hc : type_of% (@HRS.ui_comparison d)) :
    type_of% (@HRS.ui_qualitative d) := by
  intro hd s β hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ S hS hSF hν hUI t ht G hG hGm hGi u hu0 hu
  obtain ⟨C, c, hC, hc0, hcmp⟩ := hc hd hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ
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
  -- choice of the truncation level `L` for a given error budget `η`
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
  -- convergence of a nonnegative real sequence from eventual smallness
  have hconv : ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) → (∀ ε > 0, ∀ᶠ n in atTop, f n < ε) →
      Tendsto f atTop (𝓝 0) := by
    intro f hf hlim
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hlim ε hε] with n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
    exact hn
  -- from `ofReal x ≤ ofReal a + 4b` and `4b ≤ ofReal η` to `x ≤ a + η`
  have hgen : ∀ (x a η : ℝ) (b : ℝ≥0∞), 0 ≤ a → 0 ≤ η →
      ENNReal.ofReal x ≤ ENNReal.ofReal a + 4 * b → 4 * b ≤ ENNReal.ofReal η → x ≤ a + η := by
    intro x a η b ha hη hx hb
    have hq : 0 ≤ a + η := by linarith
    have h2 : ENNReal.ofReal x ≤ ENNReal.ofReal (a + η) := by
      rw [ENNReal.ofReal_add ha hη]
      exact hx.trans (by gcongr)
    exact (ENNReal.ofReal_le_ofReal_iff hq).1 h2
  constructor
  · apply hconv
    · intro n
      exact smoothDist_nonneg _ _ _
    · intro ε hε
      obtain ⟨L, hL1, hL2, hL3⟩ := hL (ε / 2) (half_pos hε)
      have hsqL : Tendsto (fun n : ℕ => C * Real.sqrt L * Real.sqrt (deltaN d s (n + 2)))
          atTop (𝓝 0) := by
        have h := hsq.const_mul (C * Real.sqrt L)
        rw [mul_zero] at h
        exact h
      filter_upwards [hsqL.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))] with n hn
      have hA := (hcmp S hS hSF hν L hL1 hL2 n).1 t ht (G n) (hG n) (hGm n) (hGi n)
      have hB := hgen _ _ _ _
        (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg L)) (Real.sqrt_nonneg _)) (half_pos hε).le hA hL3
      linarith
  · apply hconv
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

end HRS.ME.Ret

end
