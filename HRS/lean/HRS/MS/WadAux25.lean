import HRS.MS.WadAux24
import HRS.MS.WadAux8

/-!
# S8.3, packet D5^4 (Route A): the a priori estimate for classical backward solutions, definitions and `q`-facts

`S84Sol ρ a ν t M Φ w` collects the hypotheses on a classical backward solution `w` with terminal datum
`w t` of weighted size `Φ`: regularity, the mild (Duhamel) form with source `q_s = 𝓑 w_s` (`s84_Bop`),
and the continuity/growth of `q` needed to use the Mehler semigroup on it.
`S84Adm lam t M w Θ` is the weighted Hölder admissibility
`‖Dw_s(y)‖ ≤ Θ ρ_λ(s) ⟨y⟩^M`, `‖Dw_s(x')-Dw_s(x)‖ ≤ Θ ρ_λ(s)‖x'-x‖^{1/2}⟨x⟩^M`,
`ρ_λ(s) = e^{λ(t-s)}(t-s)^{-3/4}`, for `s ∈ [0,t)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The weight `ρ_λ(s) = e^{λ(t-s)} (t-s)^{-3/4}`. -/
def s84_wt (lam t s : ℝ) : ℝ := Real.exp (lam * (t - s)) * (t - s) ^ (-(3 / 4 : ℝ))

theorem s84_wt_nonneg (lam t s : ℝ) (hs : s ≤ t) : 0 ≤ s84_wt lam t s :=
  mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)

structure S84Sol (ρ : Euc d → ℝ) (a ν t M Φ : ℝ) (w : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ r ∈ Set.Icc 0 t, ContDiff ℝ 2 (w r)
  hqc : ContinuousOn (fun p : ℝ × Euc d => s84_Bop ρ (w p.1) p.2) (Set.Icc 0 t ×ˢ Set.univ)
  hqb : ∃ (K : ℝ) (p : ℕ), ∀ s ∈ Set.Icc 0 t, ∀ y, |s84_Bop ρ (w s) y| ≤ K * (1 + ‖y‖) ^ p
  mild : ∀ r ∈ Set.Icc 0 t, ∀ x, w r x =
    s83_P a ν (t - r) (w t) x + ∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) x
  term_cont : Continuous (w t)
  term_wt : Wt M Φ (w t)
  bdd : ∃ B1 B2 : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ y, ‖fderiv ℝ (w r) y‖ ≤ B1 ∧
    ‖fderiv ℝ (fderiv ℝ (w r)) y‖ ≤ B2

def S84Adm (lam t M : ℝ) (w : ℝ → Euc d → ℝ) (Θ : ℝ) : Prop :=
  ∀ s ∈ Set.Ico 0 t, (∀ y, ‖fderiv ℝ (w s) y‖ ≤ Θ * s84_wt lam t s * jbracket y ^ M) ∧
    ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
      ‖fderiv ℝ (w s) x' - fderiv ℝ (w s) x‖ ≤
        Θ * s84_wt lam t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M

theorem S84Adm.mono {lam t M : ℝ} {w : ℝ → Euc d → ℝ} {Θ Θ' : ℝ} (h : S84Adm lam t M w Θ)
    (hΘ : Θ ≤ Θ') : S84Adm lam t M w Θ' := by
  intro s hs
  obtain ⟨h1, h2⟩ := h s hs
  have hw := s84_wt_nonneg lam t s hs.2.le
  refine ⟨fun y => (h1 y).trans ?_, fun x x' hx => (h2 x x' hx).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΘ hw)
      (Real.rpow_nonneg (s83_jb_pos _).le _)
  · refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (s83_jb_pos _).le _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΘ hw) (Real.rpow_nonneg (norm_nonneg _) _)

/-- `q_s = 𝓑 w_s` has weighted growth controlled by an admissible `Θ`. -/
theorem s84_q_wt {ρ : Euc d → ℝ} {M CB lam t Θ : ℝ} {w : ℝ → Euc d → ℝ}
    (hCB : ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop ρ h x| ≤ CB * (V + H) * jbracket x ^ M)
    (hΘ : 0 ≤ Θ) (hadm : S84Adm lam t M w Θ) {s : ℝ} (hs : s ∈ Set.Ico 0 t) :
    Wt M (2 * CB * Θ * s84_wt lam t s) (fun y => s84_Bop ρ (w s) y) := by
  intro y
  have hw := s84_wt_nonneg lam t s hs.2.le
  obtain ⟨h1, h2⟩ := hadm s hs
  have := hCB (h := w s) (V := Θ * s84_wt lam t s) (H := Θ * s84_wt lam t s)
    (mul_nonneg hΘ hw) (mul_nonneg hΘ hw) h1 (fun x x' hx => by
      have := h2 x x' hx
      linarith [this]) y
  rw [Real.norm_eq_abs]
  refine this.trans (le_of_eq ?_)
  ring

/-- Interval integrability of the source in the mild form. -/
theorem s84_hint {ρ : Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (ha : 0 < a) (hν : 0 < ν)
    (sol : S84Sol ρ a ν t M Φ w) {r : ℝ} (hr : r ∈ Set.Icc 0 t) (y : Euc d) :
    IntervalIntegrable (fun s => s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) y) volume r t := by
  obtain ⟨K, p, hb⟩ := sol.hqb
  have := s83_cont_param (Φ := fun s y => s84_Bop ρ (w s) y) hr.1 hr.2 sol.hqc hb ha hν.le y
  refine ContinuousOn.intervalIntegrable ?_
  rw [Set.uIcc_of_le hr.2]
  exact this

theorem s84_fderiv_shift_sub {F : Euc d → ℝ} (hF : Differentiable ℝ F) (Δ y : Euc d) :
    DifferentiableAt ℝ (fun y => F (y + Δ) - F y) y ∧
      fderiv ℝ (fun y => F (y + Δ) - F y) y = fderiv ℝ F (y + Δ) - fderiv ℝ F y := by
  have h1 : DifferentiableAt ℝ (fun y => F (y + Δ)) y := (hF (y + Δ)).comp y (differentiableAt_id.add_const Δ)
  refine ⟨h1.sub (hF y), ?_⟩
  have e : (fun y => F (y + Δ) - F y) = (fun y => F (y + Δ)) - F := rfl
  rw [e, fderiv_sub h1 (hF y), fderiv_comp_add_right]

end HRS.MS.Wad
