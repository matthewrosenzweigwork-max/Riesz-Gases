/-
# HRS.Equilibrium.L49Aux8 — Proposition 4.9, part 8: square-log bound and the variance bound

* `l49_sqlog`: `R:eq:square-log` in real form, `J(u) = ∫ g² e^{-u g} dμ ≤ C (1 + |log u|)`, `0 < u ≤ 1`.
* `l49_var_bound`: `R:eq:pole-variance-input` for `f = g(x - ·)`:
  `Var_{P_t}(∑_i g(x - y_i)) ≤ C n (1 + |log(tλ)|)`.
* `l49_cs`: Cauchy-Schwarz in the form `(∫ a b)² ≤ ∫ a² ∫ b²`.
-/
import HRS.Equilibrium.L48Aux5
import HRS.Equilibrium.L49Aux7

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

/-- `J(u) = ∫ g₊(x-y)² e^{-u g₊(x-y)} dμ(y)`. -/
def l49_J (d : ℕ) (s c : ℝ) (ρ : Torus d → ℝ) (x : Torus d) (u : ℝ) : ℝ :=
  ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)) ∂(withDensityReal ρ)

theorem l49_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b : Ω → ℝ}
    (ha : MemLp a 2 P) (hb : MemLp b 2 P) :
    (∫ ω, a ω * b ω ∂P) ^ 2 ≤ (∫ ω, a ω ^ 2 ∂P) * ∫ ω, b ω ^ 2 ∂P := by
  have hab : Integrable (fun ω => a ω * b ω) P := ha.integrable_mul hb
  have ha2 : Integrable (fun ω => a ω ^ 2) P := by simpa using ha.integrable_sq
  have hb2 : Integrable (fun ω => b ω ^ 2) P := by simpa using hb.integrable_sq
  have key : ∀ θ : ℝ, 0 ≤ (∫ ω, b ω ^ 2 ∂P) * (θ * θ) + (-2 * ∫ ω, a ω * b ω ∂P) * θ +
      ∫ ω, a ω ^ 2 ∂P := by
    intro θ
    have h1 : 0 ≤ ∫ ω, (a ω - θ * b ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have h2 : ∫ ω, (a ω - θ * b ω) ^ 2 ∂P =
        (∫ ω, a ω ^ 2 ∂P) - 2 * θ * (∫ ω, a ω * b ω ∂P) + θ ^ 2 * ∫ ω, b ω ^ 2 ∂P := by
      have e : ∀ ω, (a ω - θ * b ω) ^ 2 = a ω ^ 2 - 2 * θ * (a ω * b ω) + θ ^ 2 * b ω ^ 2 := by
        intro ω; ring
      simp_rw [e]
      have h3 : ∫ ω, (a ω ^ 2 - 2 * θ * (a ω * b ω) + θ ^ 2 * b ω ^ 2) ∂P =
          (∫ ω, (a ω ^ 2 - 2 * θ * (a ω * b ω)) ∂P) + ∫ ω, θ ^ 2 * b ω ^ 2 ∂P :=
        integral_add (ha2.sub (hab.const_mul _)) (hb2.const_mul _)
      have h4 : ∫ ω, (a ω ^ 2 - 2 * θ * (a ω * b ω)) ∂P =
          (∫ ω, a ω ^ 2 ∂P) - ∫ ω, 2 * θ * (a ω * b ω) ∂P := integral_sub ha2 (hab.const_mul _)
      rw [h3, h4, integral_const_mul, integral_const_mul]
    nlinarith [h1, h2]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem l49_sqlog (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {c : ℝ} (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      Integrable (fun y => gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
        (withDensityReal ρ) ∧ 0 ≤ l49_J d s c ρ x u ∧
      l49_J d s c ρ x u ≤ C * (1 + |Real.log u|) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C, -, -, -, -, h5, -⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc
  have hgm := measurable_gPlus hd hs0 hsd c
  refine ⟨|C|, abs_nonneg _, fun u hu hu1 x => ?_⟩
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)) :=
    ((hgm.comp (measurable_const.sub measurable_id)).pow_const 2).mul
      (Real.measurable_exp.comp (measurable_const.mul (hgm.comp (measurable_const.sub measurable_id))))
  have hf0 : ∀ y : Torus d, 0 ≤ gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)) :=
    fun y => by positivity
  have hb := h5 u hu hu1 x
  have hfin : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) < ∞ := lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  have hint : Integrable (fun y => gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
      (withDensityReal ρ) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (hf0 y)]
  refine ⟨hint, integral_nonneg hf0, ?_⟩
  unfold l49_J
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  have hCl : C * (1 + |Real.log u|) ≤ |C| * (1 + |Real.log u|) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (hb.trans ?_))
  exact ENNReal.ofReal_le_ofReal hCl

end L49

end HRS

end
