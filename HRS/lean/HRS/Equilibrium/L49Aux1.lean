/-
# HRS.Equilibrium.L49Aux1 — Proposition 4.9 (`M:R:prop:insertion-coefficient`), part 1: calculus

## TeX-to-Lean chain for Proposition 4.9 (source lines 4389-4426)

Notation: `n = N-1`, `λ = β/N`, `g = g₊ = periodicRiesz + c ≥ 0`, `P_t = critPole x t`,
`f_i = g(x - y_i)`, `F = ∑ f_i`, `T_i = E[f_i | y_j, j ≠ i]`, `J(t) = ∫ g² e^{-tλg} dμ`,
`H = taylorH`, `D_N = insertionDefect`, `δ_N = log(eN)/N = deltaN` (at `s = d/2`).

Statement check: at `s = d/2`, `deltaN d s N = N⁻¹ log(e N)` (the middle branch of the `if`), and
`2 s = d`, so the displayed constant `β²|S^{d-1}|/d` is `|S^{d-1}|/(2s)` times `β²`; the statement
matches the TeX.  There is no junk-value loophole: `insertionDefect` contains a Bochner integral
and a `log`, but `cavity_response_proof` (clause 1) shows the integrand is integrable and
`D_N ≥ 0`, and the TeX proof only ever uses `D_N` through `R:eq:D-integral`.

1. `R:eq:D-integral`: `ofReal D_N = ∫⁻_{(0,1]} ofReal((1-t)λ²) · evariance F (P_t) dt`,
   `D_N ≤ C δ_N` (`cavity_response_proof` clause 1; the second inequality absorbs small `N`).
2. `R:eq:variance-identity` (`L49Aux7`, `l49_variance_identity`): `Var F = ∑_i (E f_i² - E T_i²)
   + ∑_i E[(F-EF)(T_i - E f_i)]` (conditional-expectation orthogonality `l49_orth`, per index `i`,
   so no exchangeability is needed for it).
3. `R:eq:offdiagonal-bound` (`L49Aux8`, `L49Aux9`, `L49Aux11`): `Var F ≤ C n (1 + |log(tλ)|)`
   (`l49_var_bound`, from `pole_variance_clause` and `critical_integrals`, `l49_sqlog`),
   `Var T_i ≤ C/N`, `E T_i² ≤ C` (`conditional_singular_observation_proof`), Cauchy-Schwarz
   (`l49_cs`): `|Var F - ∑_i E f_i²| ≤ n (K₁ + K₂ √(1+|log(tλ)|))` (`l49_V_close`).
4. `E f_i² = ∫ g² dm_i`, `m_i` the `i`-th marginal of `P_t` (exchangeability), density
   `e^{-tλg}(1 ± C√δ_N)` (`pole_prefactor`): `|E f_i² - J(tλ)| ≤ C √δ_N J(tλ)`
   (`R:eq:diagonal-reduction`; `l49_Q_close`, `L49Aux10`).
5. Time integration (`L49Aux12`, `L49Aux13`): `∫_0^1 (1-t) λ² n J(tλ) dt = n ∫ H(λ g(x-y)) dμ(y)`
   (Tonelli and `∫_0^1 (1-t) v² e^{-tv} dt = H(v)`, `l49_tonelli`, `l49_lintegral_H`), and
   `∫_0^1 |log t| dt = 1` (`l49_lintegral_log`) turn the pointwise-in-`t` bounds into
   `|D_N - n ∫ H(λ g) dμ| ≤ n λ² (A₀ + B₀)` (`l49_time_integral`).
6. `R:eq:compensated-integral` (`L49Aux2`-`L49Aux6`, the local computation): for `λ ≤ λ₀`,
   uniformly in `x`, `|∫ H(λ g(x-y)) dμ(y) - (|S^{d-1}|/d) ρ(x) λ² log(1/λ)| ≤ C λ²`
   (`l49_compensated`); the proof splits at `r_λ = λ^{1/s}`, uses `H(v) ≤ min(v, v²/2)`,
   `|H(v) - v²/2| ≤ v³` (`l49_H_*`), the local normalisation `g = |w|^{-s} + O(1)`
   (`periodicRiesz_local_singularity`), polar coordinates (`integral_radial`,
   `l49_ballConst_eq : ballConst d = sphereArea d`), the Lipschitz bound of `ρ`
   (`l49_pointwise_*`, `l49_local_abstract`).
7. Assembly (`L49Aux14`, `L49Aux15`): `n = N-1`, `λ = β/N`, `log(1/λ) = log N - log β`,
   `2 s = d`, `√δ_N (1+a) ≤ C √(log N)` (`l49_AB_bound`), `n λ² log(1/λ) = β² δ_N + O(1/N)`
   (`l49_term3`); the finitely many `N` with `β/N > λ₀` use `D_N ≤ C δ_N`.
-/
import HRS.Equilibrium.PoleCavity

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

/-! ### Elementary bounds for `H(v) = e^{-v} - 1 + v` -/

theorem l49_H_nonneg (v : ℝ) : 0 ≤ taylorH v := by
  unfold taylorH
  have := Real.add_one_le_exp (-v)
  linarith

theorem l49_H_le_self {v : ℝ} (hv : 0 ≤ v) : taylorH v ≤ v := by
  unfold taylorH
  have : Real.exp (-v) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  linarith

/-- `e^{-v} ≤ 1 - v + v²/2` for `v ≥ 0`. -/
theorem l49_exp_neg_le {v : ℝ} (hv : 0 ≤ v) : Real.exp (-v) ≤ 1 - v + v ^ 2 / 2 := by
  have key : ∀ v : ℝ, 0 ≤ v → Real.exp (-v) ≤ 1 - v + v ^ 2 / 2 := by
    intro v hv
    set f : ℝ → ℝ := fun v => 1 - v + v ^ 2 / 2 - Real.exp (-v) with hf
    have hd : ∀ v : ℝ, HasDerivAt f (-1 + v + Real.exp (-v)) v := by
      intro v
      have h1 : HasDerivAt (fun v : ℝ => Real.exp (-v)) (-Real.exp (-v)) v := by
        have := (hasDerivAt_id v).neg.exp
        simpa using this
      have h2 : HasDerivAt (fun v : ℝ => 1 - v + v ^ 2 / 2) (-1 + v) v := by
        have := ((hasDerivAt_id v).const_sub 1).add ((hasDerivAt_pow 2 v).div_const 2)
        exact this.congr_deriv (by simp)
      have := h2.sub h1
      convert this using 1
      ring
    have hd2 : ∀ v : ℝ, 0 ≤ v → 0 ≤ -1 + v + Real.exp (-v) := by
      intro v hv
      have := Real.add_one_le_exp (-v)
      linarith
    have hmono : MonotoneOn f (Set.Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (fun v _ => (hd v).continuousAt.continuousWithinAt)
        (fun v _ => (hd v).differentiableAt.differentiableWithinAt) ?_
      intro v hv
      rw [interior_Ici] at hv
      rw [(hd v).deriv]
      exact hd2 v (le_of_lt hv)
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hv) hv
    simp only [hf] at this
    simp at this
    linarith
  exact key v hv

theorem l49_H_le_sq {v : ℝ} (hv : 0 ≤ v) : taylorH v ≤ v ^ 2 / 2 := by
  unfold taylorH
  have := l49_exp_neg_le hv
  linarith

/-- `|H(v) - v²/2| ≤ v³` for `v ≥ 0`. -/
theorem l49_H_cubic {v : ℝ} (hv : 0 ≤ v) : |taylorH v - v ^ 2 / 2| ≤ v ^ 3 := by
  by_cases h1 : v ≤ 1
  · have hb := Real.exp_bound (x := -v) (by rw [abs_neg, abs_of_nonneg hv]; exact h1) (n := 3) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg,
      abs_of_nonneg hv] at hb
    norm_num at hb
    unfold taylorH
    have e : Real.exp (-v) - 1 + v - v ^ 2 / 2 =
        Real.exp (-v) - (1 + -v + (-v) ^ 2 / 2) := by ring
    rw [e]
    have e2 : (-v) ^ 2 / 2 = v ^ 2 / 2 := by ring
    rw [e2]
    refine hb.trans ?_
    have : 0 ≤ v ^ 3 := by positivity
    nlinarith
  · push Not at h1
    have hH0 := l49_H_nonneg v
    have hH1 := l49_H_le_self hv
    rw [abs_le]
    have hv3 : v ^ 2 ≤ v ^ 3 := by nlinarith
    have hv1 : v ≤ v ^ 2 := by nlinarith
    constructor <;> nlinarith

/-! ### The time integral `∫_0^1 (1-t) v² e^{-tv} dt = H(v)` -/

theorem l49_integral_H {v : ℝ} (hv : 0 ≤ v) :
    ∫ t in (0 : ℝ)..1, (1 - t) * v ^ 2 * Real.exp (-t * v) = taylorH v := by
  rcases hv.eq_or_lt with h0 | hpos
  · subst h0
    simp [taylorH]
  · set F : ℝ → ℝ := fun t => (-(1 - t) * Real.exp (-t * v) / v + Real.exp (-t * v) / v ^ 2) * v ^ 2
      with hF
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F ((1 - t) * v ^ 2 * Real.exp (-t * v)) t := by
      intro t _
      have he : HasDerivAt (fun t : ℝ => Real.exp (-t * v)) (-v * Real.exp (-t * v)) t := by
        have h1 : HasDerivAt (fun t : ℝ => -t * v) (-v) t := by
          simpa using ((hasDerivAt_id t).neg).mul_const v
        have := h1.exp
        simpa [mul_comm] using this
      have h2 : HasDerivAt (fun t : ℝ => -(1 - t)) 1 t := by
        have := ((hasDerivAt_id t).const_sub 1).neg
        exact this.congr_deriv (by simp)
      have h3 := ((h2.mul he).div_const v).add (he.div_const (v ^ 2))
      have h4 := h3.mul_const (v ^ 2)
      convert h4 using 1
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder]
    · simp only [hF, taylorH]
      field_simp
      simp
      ring
    · apply Continuous.intervalIntegrable
      fun_prop

theorem l49_lintegral_H {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * v ^ 2 * Real.exp (-t * v)) =
      ENNReal.ofReal (taylorH v) := by
  have hcont : Continuous fun t : ℝ => (1 - t) * v ^ 2 * Real.exp (-t * v) := by fun_prop
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t : ℝ => (1 - t) * v ^ 2 * Real.exp (-t * v) := by
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    have : 0 ≤ 1 - t := by linarith [ht.2]
    positivity
  have hint : IntegrableOn (fun t : ℝ => (1 - t) * v ^ 2 * Real.exp (-t * v)) (Set.Ioc (0 : ℝ) 1) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le zero_le_one,
    l49_integral_H hv]

/-! ### The logarithmic time integral -/

theorem l49_lintegral_log (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (A + B * |Real.log t|) = ENNReal.ofReal (A + B) := by
  have hint : IntegrableOn (fun t : ℝ => A + B * |Real.log t|) (Set.Ioc (0 : ℝ) 1) := by
    have h1 : IntegrableOn Real.log (Set.Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_log')
    have h2 : IntegrableOn (fun t : ℝ => |Real.log t|) (Set.Ioc (0 : ℝ) 1) := h1.abs
    exact (integrableOn_const (by simp)).add (h2.const_mul B)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun t : ℝ => A + B * |Real.log t| :=
    Eventually.of_forall fun t => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  have h1 : ∫ t in Set.Ioc (0 : ℝ) 1, (A + B * |Real.log t|) =
      ∫ t in Set.Ioc (0 : ℝ) 1, (A + B * (-Real.log t)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [abs_of_nonpos (Real.log_nonpos ht.1.le ht.2)]
  rw [h1, ← intervalIntegral.integral_of_le zero_le_one]
  have hl : IntervalIntegrable Real.log volume 0 1 := intervalIntegral.intervalIntegrable_log'
  have e3 : ∫ x in (0 : ℝ)..1, (A + B * -Real.log x) = A + B := by
    have h3 : ∫ x in (0 : ℝ)..1, (A + B * -Real.log x) =
        (∫ x in (0 : ℝ)..1, A) + ∫ x in (0 : ℝ)..1, B * -Real.log x :=
      intervalIntegral.integral_add (by simp) (hl.neg.const_mul B)
    rw [h3, intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, integral_log]
    simp
  exact e3

end L49

end HRS

end
