import HRS.MS.UniqE1c
import HRS.MS.UniqC3e

/-!
# E2 of `UniqPlan.md`, part 1: the one-variable product rule

For `g ∈ C¹([0,t])` (a derivative `g'` continuous on `[0,t]`, within `[0,t]`) and `h(σ) = ∫_0^σ f`
with `f` integrable on `[0,t]`:
`g(τ) h(τ)² = ∫_0^τ ( g' h² + 2 g h f )`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval

namespace HRS.MS.UniqE2

theorem e2_lipschitz {t : ℝ} {g g' : ℝ → ℝ}
    (hg : ∀ σ ∈ Icc (0 : ℝ) t, HasDerivWithinAt g (g' σ) (Icc 0 t) σ)
    (hg' : ContinuousOn g' (Icc 0 t)) : ∃ K : ℝ≥0, LipschitzOnWith K g (Icc 0 t) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'
  refine ⟨M.toNNReal, convex_Icc 0 t |>.lipschitzOnWith_of_nnnorm_hasDerivWithin_le hg fun σ hσ => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (hM σ hσ).trans (le_max_left _ _)

theorem e2_prod {t : ℝ} {g g' f : ℝ → ℝ}
    (hg : ∀ σ ∈ Icc (0 : ℝ) t, HasDerivWithinAt g (g' σ) (Icc 0 t) σ)
    (hg' : ContinuousOn g' (Icc 0 t)) (hf : IntegrableOn f (Icc 0 t)) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) t) :
    g τ * (∫ s in (0 : ℝ)..τ, f s) ^ 2 =
      ∫ σ in (0 : ℝ)..τ, (g' σ * (∫ s in (0 : ℝ)..σ, f s) ^ 2 +
        2 * g σ * (∫ s in (0 : ℝ)..σ, f s) * f σ) := by
  obtain ⟨K, hK⟩ := e2_lipschitz hg hg'
  have hsub : uIcc 0 τ ⊆ Icc 0 t := by
    rw [uIcc_of_le hτ.1]; exact Icc_subset_Icc le_rfl hτ.2
  have hgac : AbsolutelyContinuousOnInterval g 0 τ := (hK.mono hsub).absolutelyContinuousOnInterval
  have hfτ : IntervalIntegrable f volume 0 τ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
    exact hf.mono_set (Icc_subset_Icc le_rfl hτ.2)
  set H : ℝ → ℝ := fun σ => ∫ s in (0 : ℝ)..σ, f s with hH
  have hHac : AbsolutelyContinuousOnInterval H 0 τ :=
    hfτ.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc
  have hHH := hHac.fun_mul hHac
  have key := hgac.integral_deriv_mul_eq_sub hHH
  have H0 : H 0 = 0 := by simp [hH]
  rw [H0] at key
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι 0 τ →
      deriv g x * (H x * H x) + g x * deriv (fun x => H x * H x) x =
        g' x * H x ^ 2 + 2 * g x * H x * f x := by
    filter_upwards [hfτ.ae_hasDerivAt_integral, (countable_singleton τ).ae_notMem volume]
      with x hx hxτ hxI
    have hxI' : x ∈ uIcc 0 τ := uIoc_subset_uIcc hxI
    have hx0 : x ∈ Ioo 0 τ := by
      rw [uIoc_of_le hτ.1] at hxI
      exact ⟨hxI.1, lt_of_le_of_ne hxI.2 (fun h => hxτ (by simp [h]))⟩
    have hgd : HasDerivAt g (g' x) x := by
      have := hg x ⟨hx0.1.le, hx0.2.le.trans hτ.2⟩
      exact this.hasDerivAt (Icc_mem_nhds hx0.1 (hx0.2.trans_le hτ.2))
    have hHd : HasDerivAt H (f x) x := hx hxI' 0 left_mem_uIcc
    have hmul : HasDerivAt (fun x => H x * H x) (f x * H x + H x * f x) x := hHd.mul hHd
    rw [hgd.deriv, hmul.deriv]
    ring
  have := intervalIntegral.integral_congr_ae hae
  rw [this] at key
  simpa [hH, sq] using key.symm

end HRS.MS.UniqE2
