/-
# HRS.Equilibrium.L49Aux12 — Proposition 4.9, part 12: time integration

`l49_tonelli`: `∫_0^1 (1-t) λ² n J(tλ) dt = n ∫ H(λ g(x-y)) dμ(y)` (Tonelli and
`∫_0^1 (1-t) v² e^{-tv} dt = H(v)`).  `l49_time_integral`: with `V(t) = Var_{P_t}(F)`, the defect
satisfies `|D_N - n ∫ H(λ g) dμ| ≤ n λ² (A₀ + B₀)` (`R:eq:diagonal-reduction`).
-/
import HRS.Equilibrium.L49Aux11
import HRS.Equilibrium.L49Aux6

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

set_option maxHeartbeats 3200000 in
theorem l49_tonelli (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {c : ℝ} (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    {lam n : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) (hn : 0 ≤ n) (x : Torus d)
    (hI : Integrable (fun y => taylorH (lam * gPlus d s c (x - y))) (withDensityReal ρ)) :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam))) =
      ENNReal.ofReal (n * ∫ y, taylorH (lam * gPlus d s c (x - y)) ∂(withDensityReal ρ)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Csl, hCsl0, hsl⟩ := l49_sqlog hd hcrit hβ hρ hc
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  set g : Torus d → ℝ := fun y => gPlus d s c (x - y) with hg
  have hgm' : Measurable g := hgm.comp (measurable_const.sub measurable_id)
  have hg0 : ∀ y, 0 ≤ g y := fun y => hc _
  -- the integrand of the `t`-integral as a `y`-lintegral
  have h1 : ∀ t ∈ Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam))) =
      ∫⁻ y, ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y))))
        ∂(withDensityReal ρ) := by
    intro t ht
    have hu0 : 0 < t * lam := mul_pos ht.1 hlam0
    have hu1 : t * lam ≤ 1 := by
      have : t * lam ≤ 1 * lam := mul_le_mul_of_nonneg_right ht.2 hlam0.le
      linarith
    obtain ⟨hint, hJ0, -⟩ := hsl (t * lam) hu0 hu1 x
    have h1t : 0 ≤ 1 - t := by linarith [ht.2]
    have hc0 : 0 ≤ (1 - t) * lam ^ 2 * n := by positivity
    have e1 : (1 - t) * lam ^ 2 * (n * l49_J d s c ρ x (t * lam)) =
        ((1 - t) * lam ^ 2 * n) * l49_J d s c ρ x (t * lam) := by ring
    rw [e1, ENNReal.ofReal_mul hc0]
    unfold l49_J
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => by positivity),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul hc0]
    congr 1
    have e2 : Real.exp (-(t * lam) * gPlus d s c (x - y)) = Real.exp (-t * (lam * g y)) := by
      congr 1; simp only [hg]; ring
    rw [e2]
    simp only [hg]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioc h1]
  have hFm : Measurable (Function.uncurry fun (t : ℝ) (y : Torus d) =>
      ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y))))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((measurable_const.sub measurable_fst).mul
        ((measurable_const.mul (hgm'.comp measurable_snd)).pow_const 2)).mul
        (Real.measurable_exp.comp ((measurable_neg.comp measurable_fst).mul
          (measurable_const.mul (hgm'.comp measurable_snd))))))
  rw [lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (ν := withDensityReal ρ)
    (f := fun (t : ℝ) (y : Torus d) =>
      ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))))
    hFm.aemeasurable]
  have h2 : ∀ y, ∫⁻ t in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))) =
      ENNReal.ofReal n * ENNReal.ofReal (taylorH (lam * g y)) := by
    intro y
    have hv : 0 ≤ lam * g y := mul_nonneg hlam0.le (hg0 y)
    have e : ∀ t : ℝ, ENNReal.ofReal (n * ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y)))) =
        ENNReal.ofReal n * ENNReal.ofReal ((1 - t) * (lam * g y) ^ 2 * Real.exp (-t * (lam * g y))) :=
      fun t => ENNReal.ofReal_mul hn
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, l49_lintegral_H hv]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hH0 : ∀ y, 0 ≤ taylorH (lam * g y) := fun y => l49_H_nonneg _
  have hIg : Integrable (fun y => taylorH (lam * g y)) (withDensityReal ρ) := hI
  rw [← ofReal_integral_eq_lintegral_ofReal hIg (Eventually.of_forall hH0), ← ENNReal.ofReal_mul hn]

theorem l49_log_mul_bound {t lam : ℝ} (ht : 0 < t) (hlam : 0 < lam) :
    |Real.log (t * lam)| ≤ |Real.log t| + |Real.log lam| := by
  rw [Real.log_mul ht.ne' hlam.ne']
  exact abs_add_le _ _

theorem l49_E_bound {K₁ K₂ K₃ δs a ℓ L : ℝ} (hK₂ : 0 ≤ K₂) (hK₃ : 0 ≤ K₃) (hδ : 0 ≤ δs)
    (ha : 0 ≤ a) (hℓ : 0 ≤ ℓ) (hL0 : 0 ≤ L) (hL : L ≤ a + ℓ) :
    K₁ + K₂ * Real.sqrt (1 + L) + K₃ * δs * (1 + L) ≤
      (K₁ + K₂ * Real.sqrt (1 + a) + K₃ * δs * (1 + a)) + (K₂ + K₃ * δs) * ℓ := by
  have h1 : Real.sqrt (1 + L) ≤ Real.sqrt (1 + a) + ℓ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h2 : 1 ≤ Real.sqrt (1 + a) := Real.one_le_sqrt.2 (by linarith)
    have h3 : Real.sqrt (1 + a) ^ 2 = 1 + a := Real.sq_sqrt (by linarith)
    nlinarith [mul_nonneg hℓ (sub_nonneg.2 h2), sq_nonneg ℓ]
  have h4 : 1 + L ≤ (1 + a) + ℓ := by linarith
  have := mul_le_mul_of_nonneg_left h1 hK₂
  have h5 := mul_le_mul_of_nonneg_left h4 (mul_nonneg hK₃ hδ)
  nlinarith

end L49

end HRS

end
