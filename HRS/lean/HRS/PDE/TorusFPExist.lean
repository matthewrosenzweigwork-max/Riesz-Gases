import HRS.PDE.TorusFPExistAux18

/-!
# D1: existence of weak solutions of the torus Fokker–Planck equation (proof of `d1_fp_exists`)

Relocated proof of the frozen specification `HRS.d1_fp_exists` (`HRS/PDE/TorusFPSpec.lean`; the
statement there is unchanged and is left as it was).

Route: duality with the classical backward solutions `d1_backward_classical`.

* `Aux1`-`Aux3`: backward maximum principle for classical solutions (`d1_backward_nonneg`), linear
  combinations, constants, time shift, the sup-norm contraction `d1_backward_abs_le` and uniqueness
  `d1_backward_unique` of `D1BackwardSolution`;
* `Aux4`-`Aux6`: the operator `ψ ↦ U^{0,t}ψ` on smooth data (`d1_P`), extension of the positive normalised
  functional `ψ ↦ ∫ U^{0,t}ψ dμ₀` from smooth to continuous functions and the Riesz–Markov–Kakutani
  theorem, giving the probability measures `μ_t` (`d1_mu`);
* `Aux7`-`Aux8`: narrow continuity of `t ↦ μ_t`;
* `Aux9`-`Aux11`: the semigroup identity `⟨U^{0,h}φ, μ_s⟩ = ⟨U^{0,s+h}φ, μ₀⟩` and the weak equation for
  smooth time-independent tests (right derivative via uniform convergence of difference quotients);
* `Aux12`-`Aux14`: `C²` approximation of `C²` functions by smooth ones (mollification) and the weak
  equation for `C²` time-independent tests;
* `Aux15`-`Aux18`: joint continuity for `C^{1,2}` tests, right derivative of `s ↦ ∫ f_s dμ_s` and,
  here, the weak equation `eqT` by the fundamental theorem of calculus for right derivatives.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d1_fp_exists_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀] :
    ∃ μ : ℝ → Measure (Torus n), D1WeakSolution κ (d1_gradDrift U) T μ ∧ μ 0 = μ₀ := by
  refine ⟨d1_mu hn hκ hU μ₀, ⟨?_, ?_, ?_⟩, d1_mu_of_nonpos hn hκ hU μ₀ le_rfl⟩
  · intro t _
    have := d1_mu_prob hn hκ hU μ₀ t
    infer_instance
  · intro ψ hψ
    exact d1_narrow hn hκ hU μ₀ hψ T
  · intro τ hτ f ft hf
    have hb := d1_gradDrift_continuous hU
    rcases hτ.1.eq_or_lt with rfl | hτpos
    · simp
    have hcont : ContinuousOn (fun s => ∫ x, f s x ∂(d1_mu hn hκ hU μ₀ s)) (Set.Icc 0 τ) :=
      d1_continuousOn_integral_H hn hκ hU μ₀ hf.continuous_f
    have hgc : ContinuousOn (fun s => ∫ x, (ft s x + d1_gen κ (d1_gradDrift U) (f s) x)
        ∂(d1_mu hn hκ hU μ₀ s)) (Set.Icc 0 τ) :=
      d1_continuousOn_integral_H hn hκ hU μ₀
        (H := fun r x => ft r x + d1_gen κ (d1_gradDrift U) (f r) x)
        (hf.cont_time_deriv.add (hf.continuous_gen hb))
    have hint : IntervalIntegrable (fun s => ∫ x, (ft s x + d1_gen κ (d1_gradDrift U) (f s) x)
        ∂(d1_mu hn hκ hU μ₀ s)) volume 0 τ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hτpos.le]; exact hgc
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτpos.le hcont
      (fun s hs => d1_G_hasDerivWithinAt hn hκ hU μ₀ hτpos hf ⟨hs.1.le, hs.2⟩) hint
    rw [intervalIntegral.integral_of_le hτpos.le, ← integral_Icc_eq_integral_Ioc] at this
    linarith

example := (@d1_fp_exists_proof : type_of% @d1_fp_exists)

end HRS
