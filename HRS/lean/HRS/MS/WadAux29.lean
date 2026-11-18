import HRS.MS.WadAux28

/-!
# S8.3, packet D5^8 (Route A): the a priori estimate `‖w_r‖_{C_M} ≤ K ‖w_t‖_{C_M}`

* `s84_step`: one Gronwall step, `Θ ↦ 3^M (K₁T^{1/4}+K₂)(Φ + 2C_B Θ ε)`.
* `s84_zero_bound`: from admissibility, the zero-order bound of `w_r`.
* `s84_apriori`: for every classical solution (`S84Sol`) on `[0,t]`, `t ≤ T`:
  `|w_r(y)| ≤ K Φ ⟨y⟩^M`, `K = K(d,M,a,ν,T,ρ)` independent of the solution and of `t`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- One step of the Gronwall iteration. -/
theorem s84_step {a ν T M Φ lam εk t K₂ : ℝ} {ρ : Euc d → ℝ} {w : ℝ → Euc d → ℝ} {CB Θ : ℝ}
    (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) (htT : t ≤ T) (hK₂0 : 0 ≤ K₂)
    (hK₂ : ∀ {C : ℝ} {g : Euc d → ℝ}, Continuous g → Wt M C g → ∀ {τ : ℝ}, 0 < τ → τ ≤ T →
      ∀ {x x' : Euc d}, ‖x' - x‖ ≤ 1 / 4 →
      ‖fderiv ℝ (s83_P a ν τ g) x' - fderiv ℝ (s83_P a ν τ g) x‖ ≤
        K₂ * C * τ ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M)
    (hCB : ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop ρ h x| ≤ CB * (V + H) * jbracket x ^ M)
    (hCB0 : 0 ≤ CB) (sol : S84Sol ρ a ν t M Φ w) (hΘ : 0 ≤ Θ) (hlam : 0 ≤ lam) (hεk : 0 ≤ εk)
    (hker : ∀ r : ℝ, 0 ≤ r → r < t → (∫ s in r..t, (s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ))))
    (hadm : S84Adm lam t M w Θ) :
    S84Adm lam t M w (3 ^ M * (s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂) * (Φ + 2 * CB * Θ * εk)) := by
  intro r hr
  have hw0 := s84_wt_nonneg lam t r hr.2.le
  have hK₁0 : 0 ≤ s84_K1 d M a ν T := s84_K1_nonneg M ha hν
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  have hT0 : 0 ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith [hr.1, hr.2]) _
  have hQ0 : 0 ≤ Φ + 2 * CB * Θ * εk := by positivity
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · refine (s84_step_sup ha hν hM htT hCB hCB0 sol hΘ hlam hεk hadm hr (hker r hr.1 hr.2) y).trans ?_
    have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    have : s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) ≤ s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂ := by linarith
    calc 3 ^ M * jbracket y ^ M * s84_wt lam t r * (s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) * (Φ + 2 * CB * Θ * εk))
        ≤ 3 ^ M * jbracket y ^ M * s84_wt lam t r *
            ((s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂) * (Φ + 2 * CB * Θ * εk)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hQ0) (by positivity)
      _ = _ := by ring
  · refine (s84_step_holder ha hν hM htT hK₂0 hK₂ hCB hCB0 sol hΘ hlam hεk hadm hr (hker r hr.1 hr.2)
      x x' hx).trans ?_
    have hj := Real.rpow_nonneg (s83_jb_pos x).le M
    have hS := Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)
    have : K₂ ≤ s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂ := by
      have := mul_nonneg hK₁0 hT0
      linarith
    calc 3 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) * s84_wt lam t r * (K₂ * (Φ + 2 * CB * Θ * εk))
        ≤ 3 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) * s84_wt lam t r *
            ((s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂) * (Φ + 2 * CB * Θ * εk)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hQ0) (by positivity)
      _ = _ := by ring

end HRS.MS.Wad
