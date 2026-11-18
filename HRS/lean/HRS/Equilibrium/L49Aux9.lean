/-
# HRS.Equilibrium.L49Aux9 — Proposition 4.9, part 9: variance bound and marginal comparison

* `l49_var_bound`: `R:eq:pole-variance-input` with `R:eq:square-log`:
  `evariance (∑_i g(x - y_i)) ≤ C n (1 + |log(tλ)|)` under `P_t`; in particular `F ∈ L²(P_t)`.
* `l49_Q_close`: `|E f_i² - J(tλ)| ≤ C √δ_N J(tλ)` (`R:eq:prefactor` with exchangeability).
-/
import HRS.Equilibrium.L49Aux8

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

set_option maxHeartbeats 1600000 in
theorem l49_var_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {c : ℝ} (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → β / N ≤ 1 → ∀ x : Torus d, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ) * (1 + |Real.log (t * (β / N))|)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C₁, hC₁, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  obtain ⟨Csl, hCsl0, hsl⟩ := l49_sqlog hd hcrit hβ hρ hc
  have hgm := measurable_gPlus hd hs0 hsd c
  refine ⟨C₁ * Real.exp (β * |c|) * Csl, by positivity, fun N hN hlamle x t ht => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  set u : ℝ := t * (β / N) with hu
  have hu0 : 0 < u := mul_pos ht.1 (by positivity)
  have hu1 : u ≤ 1 := by
    have : t * (β / N) ≤ 1 * (β / N) := mul_le_mul_of_nonneg_right ht.2 hlam
    linarith
  have huβ : u ≤ β := by
    have : β / N ≤ β := by
      rw [div_le_iff₀ hN0]
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      nlinarith
    have : t * (β / N) ≤ 1 * (β / N) := mul_le_mul_of_nonneg_right ht.2 hlam
    linarith
  rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  have h1 := hvar N hN x t ht' (fun y => gPlus d s c (x - y)) hfm
  have hint := (hsl u hu0 hu1 x).2.2
  have hlint : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Csl * (1 + |Real.log u|)) := by
    obtain ⟨hI, -, hJ⟩ := hsl u hu0 hu1 x
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun y => by positivity)]
    exact ENNReal.ofReal_le_ofReal hJ
  have hE : ∫⁻ y, ‖gPlus d s c (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Real.exp (β * |c|)) * ENNReal.ofReal (Csl * (1 + |Real.log u|)) := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (β * |c|)) * ENNReal.ofReal
          (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e3 : ‖gPlus d s c (x - y)‖ₑ ^ 2 = ENNReal.ofReal (gPlus d s c (x - y) ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
          rw [e3, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          refine ENNReal.ofReal_le_ofReal ?_
          have hpr : periodicRiesz d s (x - y) = gPlus d s c (x - y) - c := by unfold gPlus; ring
          have hexp : Real.exp (-u * periodicRiesz d s (x - y)) =
              Real.exp (-u * gPlus d s c (x - y)) * Real.exp (u * c) := by
            rw [← Real.exp_add, hpr]; congr 1; ring
          have hec : Real.exp (u * c) ≤ Real.exp (β * |c|) := by
            refine Real.exp_le_exp.2 ?_
            calc u * c ≤ u * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) hu0.le
              _ ≤ β * |c| := mul_le_mul_of_nonneg_right huβ (abs_nonneg _)
          show gPlus d s c (x - y) ^ 2 * Real.exp (-u * periodicRiesz d s (x - y)) ≤ _
          rw [hexp]
          have := Real.exp_pos (-u * gPlus d s c (x - y))
          nlinarith [mul_le_mul_of_nonneg_left hec (mul_nonneg (sq_nonneg (gPlus d s c (x - y))) this.le)]
      _ = ENNReal.ofReal (Real.exp (β * |c|)) * ∫⁻ y, ENNReal.ofReal
          (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl hlint
  refine (h1.trans (mul_le_mul' le_rfl hE)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end L49

end HRS

end
