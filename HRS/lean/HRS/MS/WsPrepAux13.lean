import HRS.MS.WsPrepAux12
import HRS.MS.GenPathAux36

/-!
# S21R packet 13: a.e. measurability of the particle window `flucPathW` (conjunct 1 of `S21PrepMain`)

`s21p_fluc_window_aemeas`: for a particle path `X` (measurable at every time, a.s. continuous in the configuration coordinates) and
mean-field densities `ρ` that are probability densities on `[0, a₀ + T]` and weakly continuous there, the window
`flucPathW m T a₀ σ X ρ` (`m > d`) is a.e. measurable.  This is `s56_fluc_aemeas` (a = 0, `WholeSetup`) for a window start `a₀ ≥ 0`
and for a mean-field path that is not a `WholeSetup` (the hypotheses are exactly those of `s56_xi_cont_time`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole

variable {d : ℕ}

theorem s21p_fluc_window_aemeas (hd : 1 ≤ d) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : (d : ℝ) < m)
    {a₀ T : ℝ} (ha₀ : 0 ≤ a₀) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (ρ : ℝ → Euc d → ℝ) (σ : ℝ)
    (hXm : ∀ t, Measurable (X t)) (hXc : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (hprob : ∀ t ∈ Icc (0 : ℝ) (a₀ + T), IsProbDensity (ρ t))
    (hcont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Icc (0 : ℝ) (a₀ + T))) :
    AEMeasurable (flucPathW m T a₀ σ X ρ) P := by
  set Y : ℝ → Ω → OscDual d m := fun t ζ =>
    σ • OscDual.ofMeasureDiff m (empirical (X (Real.toNNReal t) ζ)) (withDensityReal (ρ t)) with hY
  have hmem : ∀ u ∈ Icc (0 : ℝ) T, a₀ + u ∈ Icc (0 : ℝ) (a₀ + T) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hmeas : ∀ u ∈ Icc (0 : ℝ) T, Measurable (fun ζ => Y (a₀ + u) ζ) := by
    intro u hu
    have := HRS.MS.Thm.cb_withDensityReal_isProb (hprob _ (hmem u hu))
    exact (HRS.MS.GenPath.s56_xi_cont_config hd hm σ hN (withDensityReal (ρ (a₀ + u)))).measurable.comp
      (hXm _)
  have hc : ∀ᵐ ζ ∂P, ContinuousOn (fun u => Y (a₀ + u) ζ) (Icc 0 T) := by
    filter_upwards [hXc] with ζ hζ
    have h := HRS.MS.GenPath.s56_xi_cont_time hd hm σ hN ρ hprob hcont (fun t => X (Real.toNNReal t) ζ)
      (fun i => (hζ i).comp continuous_real_toNNReal)
    exact h.comp (continuous_const.add continuous_id).continuousOn hmem
  have h := HRS.GF.gfb4_aemeasurable_windowPath P hT (fun u ζ => Y (a₀ + u) ζ) hmeas hc
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  have e : flucPathW m T a₀ σ X ρ = fun ζ => windowPathOf m T 0 (fun u => Y (a₀ + u) ζ) := by
    funext ζ
    unfold flucPathW
    exact s21p_wpo_shift m T a₀ (fun t => Y t ζ)
  rw [e]
  exact h

end HRS.Whole
