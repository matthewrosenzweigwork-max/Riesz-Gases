import HRS.MS.WadAux58

/-!
# S8.3, packet S8D-2, part 5: far-field bound of classical solutions at time `0`

`s8d_P_abs_le`: the Mehler average of a function bounded by `α⟨y⟩^M + γ` is bounded by `α K₀ ⟨x⟩^M + γ`.
`s8d_tail_classical`: for every `ε > 0` there is `R` such that every frozen classical adjoint solution `w` on
`[0,1]` with terminal datum `|φ| ≤ Φ⟨x⟩^M` satisfies `|w_0(x)| ≤ Φ (e^{-aM} + ε) ⟨x⟩^M` for `‖x‖ ≥ R`
(Mehler tail `s83_P_tail_bound` for the free part, `s8d_B_decay` and the Gronwall bounds `s8d_apriori_adm` for the
Duhamel remainder).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_P_abs_le {g : Euc d → ℝ} {M α γ : ℝ} (hM : 0 ≤ M) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hb : ∀ y, |g y| ≤ α * jbracket y ^ M + γ) {a ν τ : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (x : Euc d) :
    |s83_P a ν τ g x| ≤ α * (2 ^ M * mom d M (Real.sqrt (ν / a))) * jbracket x ^ M + γ := by
  have hj1 : ∀ y : Euc d, 1 ≤ jbracket y ^ M := fun y => Real.one_le_rpow (s83_one_le_jb y) hM
  have hjc : Continuous (fun y : Euc d => jbracket y ^ M) := s83_jb_rpow_cont M
  have hwj : Wt M 1 (fun y : Euc d => jbracket y ^ M) := fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos y).le _)]; simp
  have hσ := s83_abs_ms_le ha hν hτ
  have hc := s83_abs_mc_le_one ha.le hτ
  set Y : Euc d → Euc d := fun z => s83_mc a τ • x + s83_ms a ν τ • z with hY
  have i1 : Integrable (fun z : Euc d => jbracket (Y z) ^ M) (stdGaussian (Euc d)) :=
    s83_int_shift hjc hM hwj hσ (c := s83_mc a τ) x
  have hbi : Integrable (fun z : Euc d => α * jbracket (Y z) ^ M + γ) (stdGaussian (Euc d)) :=
    (i1.const_mul α).add (integrable_const γ)
  have hle : ‖s83_P a ν τ g x‖ ≤ ∫ z, (α * jbracket (Y z) ^ M + γ) ∂(stdGaussian (Euc d)) := by
    refine norm_integral_le_of_norm_le hbi (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]; exact hb _
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  rw [integral_add (i1.const_mul α) (integrable_const γ), integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  have hP := s83_P_wt hjc hM hwj ha hν hτ x
  rw [Real.norm_eq_abs] at hP
  have e : ∫ z, jbracket (Y z) ^ M ∂(stdGaussian (Euc d)) = s83_P a ν τ (fun y => jbracket y ^ M) x := rfl
  rw [e]
  have := le_abs_self (s83_P a ν τ (fun y => jbracket y ^ M) x)
  nlinarith [mul_le_mul_of_nonneg_left (this.trans hP) hα]

end HRS.MS.Wad
