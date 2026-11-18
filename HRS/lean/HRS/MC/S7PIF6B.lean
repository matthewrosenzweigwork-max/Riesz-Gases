import HRS.MC.S7PIF6A
import HRS.MC.S7PIF4F

/-!
# Packet piF6, part B: bounds

* `S7PIF6_grad_bound`: `∇ U^{r,τ} ψ` is bounded on `[0,τ] × 𝕋^d` (joint continuity on a compact set);
* `S7PIF6_heat_fderiv_bound`: `|D (gaussHeat S G s) c u| ≤ ‖DG‖_∞ ‖u‖` for every covariance;
* the bound of the diffusion coefficient `Φc = √N · empiricalNoiseIntegrand`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIF6

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {d : ℕ}

/-- the gradient of the propagator is bounded on `[0,τ] × 𝕋^d` -/
theorem S7PIF6_grad_bound (R : Regime d) {τ : ℝ} (hτ : 0 ≤ τ) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) :
    ∃ C : ℝ, ∀ r ∈ Set.Icc 0 τ, ∀ (x : Torus d) (j : Fin d),
      |Torus.grad (propagator R.D R.ρ r τ ψ) x j| ≤ C := by
  rcases hτ.eq_or_lt with h0 | hpos
  · subst h0
    have hc : Continuous (Torus.grad (propagator R.D R.ρ 0 0 ψ)) :=
      HRS.PDE.MFLinear.continuous_grad (S7PIS3_prop_isCk R.D R.ρ 0 ψ le_rfl le_rfl)
    obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨C, fun r hr x j => ?_⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    subst hr0
    exact (PiLp.norm_apply_le (Torus.grad (propagator R.D R.ρ 0 0 ψ) x) j).trans (hC x (Set.mem_univ _))
  · obtain ⟨F, hFcl, hFeq⟩ := HRS.MC.L2C3.l2c3_classical R hpos hψ
    have hcj : ∀ j : Fin d, ∃ C : ℝ, ∀ p : Set.Icc (0 : ℝ) τ × Torus d,
        ‖Torus.partialDeriv j (F p.1) p.2‖ ≤ C := by
      intro j
      have hc := HRS.PDE.MFLinear.continuous_partialDeriv_prod hFcl j
      obtain ⟨C, hC⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) τ × Torus d)).exists_bound_of_continuousOn
        hc.continuousOn
      exact ⟨C, fun p => hC p (Set.mem_univ _)⟩
    choose C hC using hcj
    refine ⟨∑ j, |C j|, fun r hr x j => ?_⟩
    rw [hFeq r hr, HRS.Commutator.StressAux.grad_apply]
    have := hC j (⟨r, hr⟩, x)
    simp only [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))

/-- the derivative of a Gaussian average of a `C_b^1` function is bounded by `‖DG‖_∞` -/
theorem S7PIF6_heat_fderiv_bound {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 4 G) (s : ℝ) (c u : EuclideanSpace ℝ (Fin q)) :
    |fderiv ℝ (gaussHeat S G s) c u| ≤ (⨆ z, ‖iteratedFDeriv ℝ 1 G z‖) * ‖u‖ := by
  have hG1 : MemCb 1 G := ⟨hG.1.of_le (by norm_num), fun j hj => hG.2 j (by omega)⟩
  have h1 : iteratedFDeriv ℝ 1 (gaussHeat S G s) c = ∫ x, iteratedFDeriv ℝ 1 G (c + x)
      ∂(multivariateGaussian 0 (S s)) :=
    S7PIS3_heat_deriv (multivariateGaussian 0 (S s)) hG1 le_rfl c
  have h2 : ‖iteratedFDeriv ℝ 1 (gaussHeat S G s) c‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖ := by
    rw [h1]
    have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian 0 (S s))
      (f := fun x => iteratedFDeriv ℝ 1 G (c + x)) (C := ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖)
      (Filter.Eventually.of_forall fun x => S7PIS3_cb_bound hG1 le_rfl (c + x))
    simpa using this
  have h3 : fderiv ℝ (gaussHeat S G s) c u = iteratedFDeriv ℝ 1 (gaussHeat S G s) c ![u] := by
    rw [iteratedFDeriv_one_apply]; rfl
  rw [h3]
  have := (iteratedFDeriv ℝ 1 (gaussHeat S G s) c).le_opNorm ![u]
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  have hp : ∏ i : Fin 1, ‖(![u] : Fin 1 → EuclideanSpace ℝ (Fin q)) i‖ = ‖u‖ := by simp
  rw [hp]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/-- the noise integrands of the observations are bounded (uniformly in time, configuration, path and index) -/
theorem S7PIF6_noise_bound (R : Regime d) {N : ℕ} {Ω : Type} (X : ℝ≥0 → Ω → Config d N) {q : ℕ}
    (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, 0 ≤ t i) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ω k i,
      |empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω k| ≤ C := by
  choose C hC using fun i => S7PIF6_grad_bound R (ht i) (hφ i)
  refine ⟨(Real.sqrt (2 * R.D.invβ) / N) * ∑ i, |C i|, by positivity, fun s ω k i => ?_⟩
  unfold empiricalNoiseIntegrand
  by_cases hs : s ∈ Set.Icc 0 (t i)
  · rw [if_pos hs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (2 * R.D.invβ) / N)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (hC i s hs _ _).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)))
  · rw [if_neg hs]
    simp only [abs_zero]
    positivity

end HRS.MC.Sec7.S7PIF6

end
