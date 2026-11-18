import HRS.MS.TransOpAux11

/-!
# S611 packet P2e: `L²`-continuity of translations of a Hermite function, and strong continuity of `c ↦ Λ_c`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_l2_continuity (β : MultiIndex d) (c₀ : Euc d) :
    Tendsto (fun c : Euc d => ∫ y, (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2)
      (𝓝 c₀) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := s611_hermiteFunD_gauss_bound β
  set ρ : ℝ := ‖c₀‖ + 1 with hρ
  set B : Euc d → ℝ := fun y => 4 * C ^ 2 * Real.exp (ρ ^ 2 / 4) * Real.exp (-((1 / 8) * ‖y‖ ^ 2)) with hB
  have hBint : Integrable B := (s611_integrable_gauss (d := d) (c := 1 / 8) (by norm_num)).const_mul _
  have hcont : ∀ c : Euc d, Continuous (fun y : Euc d => (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2) :=
    fun c => by
      have := (contDiff_hermiteFunD β).continuous
      fun_prop
  have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (l := 𝓝 c₀)
    (F := fun c y => (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2)
    (f := fun _ => (0 : ℝ)) B
    (Filter.Eventually.of_forall fun c => (hcont c).aestronglyMeasurable)
    ?_ hBint ?_
  · simpa using key
  · have hball : ∀ᶠ c in 𝓝 c₀, c ∈ Metric.ball c₀ 1 := Metric.ball_mem_nhds c₀ one_pos
    filter_upwards [hball] with c hc
    refine Filter.Eventually.of_forall fun y => ?_
    have hcn : ‖c‖ ≤ ρ := by
      have : dist c c₀ < 1 := hc
      rw [dist_eq_norm] at this
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ ≤ ρ := by rw [hρ]; linarith
    have hc0n : ‖c₀‖ ≤ ρ := by rw [hρ]; linarith
    have gbound : ∀ z : Euc d, ‖z‖ ≤ ρ → ∀ y : Euc d, (hermiteFunD β (y - z)) ^ 2 ≤
        C ^ 2 * Real.exp (ρ ^ 2 / 4) * Real.exp (-((1 / 8) * ‖y‖ ^ 2)) := by
      intro z hz y
      have h1 := hC (y - z)
      have h2 : (hermiteFunD β (y - z)) ^ 2 ≤ (C * Real.exp (-(‖y - z‖ ^ 2 / 8))) ^ 2 := by
        rw [← sq_abs (hermiteFunD β (y - z))]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      refine h2.trans ?_
      rw [mul_pow, sq (Real.exp _), ← Real.exp_add, mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sq_nonneg C)
      have hyz : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by
        calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
      have : ‖y‖ ^ 2 ≤ 2 * ‖y - z‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
        have h3 := pow_le_pow_left₀ (norm_nonneg y) hyz 2
        nlinarith [sq_nonneg (‖y - z‖ - ‖z‖), norm_nonneg (y - z), norm_nonneg z]
      have hz2 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      nlinarith
    have g1 := gbound c hcn y
    have g2 := gbound c₀ hc0n y
    have hsq : (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2 ≤
        2 * (hermiteFunD β (y - c)) ^ 2 + 2 * (hermiteFunD β (y - c₀)) ^ 2 := by
      nlinarith [sq_nonneg (hermiteFunD β (y - c) + hermiteFunD β (y - c₀))]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    refine hsq.trans ?_
    simp only [hB]
    nlinarith [Real.exp_pos (ρ ^ 2 / 4), Real.exp_pos (-((1 / 8) * ‖y‖ ^ 2))]
  · refine Filter.Eventually.of_forall fun y => ?_
    have h := (contDiff_hermiteFunD β).continuous
    have : Tendsto (fun c : Euc d => (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2) (𝓝 c₀)
        (𝓝 ((hermiteFunD β (y - c₀) - hermiteFunD β (y - c₀)) ^ 2)) := by
      have hc : Continuous (fun c : Euc d => (hermiteFunD β (y - c) - hermiteFunD β (y - c₀)) ^ 2) := by
        fun_prop
      exact hc.tendsto c₀
    simpa using this

end HRS.MS.TransOp

end
