import HRS.MC.S7E3aAux6

/-!
# Packets `s7_E3a/b`, file 7: from the two-sided bounds to the ratio limit
-/

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section

namespace HRS.MC.Sec7.E3Aux7

theorem e3_ratio {X T D : ℝ → ℝ} (hD : Tendsto D (𝓝[>] 0) atTop)
    (hT : Tendsto (fun ε => T ε / (2 * D ε)) (𝓝[>] 0) (𝓝 1))
    (hup : ∀ᶠ ε in 𝓝[>] (0 : ℝ), X ε ≤ T ε / 2)
    (hlow : ∀ η : ℝ, 0 < η → ∃ K : ℝ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 - 4 * η) / 2 * T ε - K ≤ X ε) :
    Tendsto (fun ε => X ε / D ε) (𝓝[>] 0) (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro γ0 hγ0
  set γ : ℝ := min γ0 1 with hγ
  have hγpos : 0 < γ := lt_min hγ0 one_pos
  have hγ1 : γ ≤ 1 := min_le_right _ _
  have hγle : γ ≤ γ0 := min_le_left _ _
  obtain ⟨K, hK⟩ := hlow (γ / 8) (by positivity)
  have hT' := (Metric.tendsto_nhds.1 hT) (γ / 4) (by positivity)
  have hDpos := hD.eventually_gt_atTop 0
  have hDbig := hD.eventually_gt_atTop (8 * |K| / γ)
  filter_upwards [hup, hK, hT', hDpos, hDbig] with ε h1 h2 h3 h4 h5
  have hD2 : 0 < 2 * D ε := by linarith
  set r := T ε / (2 * D ε) with hr
  have hr1 : |r - 1| < γ / 4 := by simpa [Real.dist_eq] using h3
  have hr2 := abs_lt.1 hr1
  have hTr : T ε = r * (2 * D ε) := by rw [hr]; field_simp
  have hKD : |K| / D ε < γ / 8 := by
    rw [div_lt_iff₀ h4]
    have := (div_lt_iff₀ hγpos).1 h5
    nlinarith [this]
  have hKD' : K / D ε ≤ |K| / D ε := div_le_div_of_nonneg_right (le_abs_self K) h4.le
  have hKD'' : -(|K| / D ε) ≤ K / D ε := by
    have := div_le_div_of_nonneg_right (neg_abs_le K) h4.le
    rwa [neg_div] at this
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- lower bound
    have : (1 - 4 * (γ / 8)) / 2 * T ε - K ≤ X ε := h2
    have h6 : X ε / D ε ≥ ((1 - 4 * (γ / 8)) / 2 * T ε - K) / D ε :=
      div_le_div_of_nonneg_right this h4.le
    have h7 : ((1 - 4 * (γ / 8)) / 2 * T ε - K) / D ε = (1 - γ / 2) * r - K / D ε := by
      rw [hTr]; field_simp; ring
    have h8 : (1 - γ / 2) * r ≥ (1 - γ / 2) * (1 - γ / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  · -- upper bound
    have h6 : X ε / D ε ≤ T ε / 2 / D ε := div_le_div_of_nonneg_right h1 h4.le
    have h7 : T ε / 2 / D ε = r := by rw [hTr]; field_simp
    linarith

end HRS.MC.Sec7.E3Aux7

end
