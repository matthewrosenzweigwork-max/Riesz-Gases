import HRS.MS.WadAux50

/-!
# S8.3, packet S8D-1 (positive-time smoothing), part 1: the admissible constant of the a priori estimate

`s8d_apriori_adm`: the Gronwall fixed point `S84Adm lam t M w (K Φ)` of the proof of `s84_apriori`
(`lam`, `K` independent of the solution and of `t ≤ T`): weighted `C^{1,1/2}` bounds of the classical solution.
`s8d_adm_classical`: for a frozen classical adjoint solution with `Wt M Φ φ` datum the gradient of `f_0` obeys
`‖Df_0(y)‖ ≤ K Φ t^{-3/4}⟨y⟩^M` and the `1/2`-Hölder bound with the same constant.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_apriori_adm (hd : 2 ≤ d) {a ν T M : ℝ} (ha : 0 < a) (hν : 0 < ν) (hT : 0 < T) (hM : 0 ≤ M)
    {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) :
    ∃ lam K : ℝ, 0 ≤ lam ∧ 0 ≤ K ∧ ∀ {t Φ : ℝ} {w : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      S84Sol ρ a ν t M Φ w → S84Adm lam t M w (K * Φ) := by
  obtain ⟨CB, hCB0, hCB⟩ := s84_B_bound hd hρ hM
  obtain ⟨K₂, hK₂0, hK₂⟩ := s84_P_fderiv_holder (d := d) (a := a) (ν := ν) (T := T) (M := M) ha hν hM
  set K₁ : ℝ := s84_K1 d M a ν T with hK₁
  have hK₁0 : 0 ≤ K₁ := s84_K1_nonneg M ha hν
  have hT0 : 0 ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg hT.le _
  set Kst : ℝ := K₁ * T ^ (1 / 4 : ℝ) + K₂ with hKst
  have hKst0 : 0 ≤ Kst := by positivity
  set c0 : ℝ := 3 ^ M * Kst * (2 * CB) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set εk : ℝ := 1 / (2 * (c0 + 1)) with hεk
  have hεk0 : 0 < εk := by positivity
  obtain ⟨lam, hlam0, hlam⟩ := s84_kernel hT hεk0
  refine ⟨lam, 2 * (3 ^ M * Kst), hlam0.le, by positivity, ?_⟩
  intro t Φ w ht htT sol
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  have hker : ∀ r' : ℝ, 0 ≤ r' → r' < t → (∫ s in r'..t, (s - r') ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      εk * (Real.exp (lam * (t - r')) * (t - r') ^ (-(3 / 4 : ℝ))) := fun r' hr0 hr't =>
    hlam r' t hr't (by linarith)
  have hstep : ∀ Θ : ℝ, 0 ≤ Θ → S84Adm lam t M w Θ →
      S84Adm lam t M w (3 ^ M * Kst * Φ + Θ / 2) := by
    intro Θ hΘ hadm
    have := s84_step ha hν hM htT hK₂0 hK₂ hCB hCB0 sol hΘ hlam0.le hεk0.le hker hadm
    refine this.mono ?_
    have hεc : c0 * εk ≤ 1 / 2 := by
      rw [hεk, ← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : 3 ^ M * Kst * (2 * CB * Θ * εk) = (c0 * εk) * Θ := by rw [hc0]; ring
    calc 3 ^ M * (K₁ * T ^ (1 / 4 : ℝ) + K₂) * (Φ + 2 * CB * Θ * εk)
        = 3 ^ M * Kst * Φ + (c0 * εk) * Θ := by rw [← this, hKst]; ring
      _ ≤ 3 ^ M * Kst * Φ + Θ / 2 := by
          have := mul_le_mul_of_nonneg_right hεc hΘ
          linarith
  obtain ⟨Θ₀, hΘ₀, hadm₀⟩ := s84_adm_start sol hM ht htT hlam0.le
  have hA : 0 ≤ 3 ^ M * Kst * Φ := by positivity
  have hfix := s84_adm_fix hA ⟨Θ₀, hΘ₀, hadm₀⟩ hstep
  have e : 2 * (3 ^ M * Kst) * Φ = 2 * (3 ^ M * Kst * Φ) := by ring
  rw [e]
  exact hfix

/-- The gradient and Hölder bounds of a frozen classical solution at time `0`. -/
theorem s8d_adm_classical (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ f → Wt M Φ φ →
      (∀ y, ‖fderiv ℝ (f 0) y‖ ≤ K * Φ * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M) ∧
      ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ (f 0) x' - fderiv ℝ (f 0) x‖ ≤
          K * Φ * t ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
  obtain ⟨lam, K, hlam, hK0, hK⟩ := s8d_apriori_adm hd ha (inv_pos.2 hβ) hT hM
    (s84_thermal_gaussReg hd ha hβ hρ)
  refine ⟨K * Real.exp (lam * T), by positivity, ?_⟩
  intro t Φ φ f ht htT hf hφ
  have hadm := hK ht htT (s84_sol_of_classical a β ha hβ ρβ ht hf hφ)
  obtain ⟨h1, h2⟩ := hadm 0 ⟨le_rfl, ht⟩
  have hΦ0 : 0 ≤ Φ := hφ.nonneg
  have hw : s84_wt lam t 0 ≤ Real.exp (lam * T) * t ^ (-(3 / 4 : ℝ)) := by
    unfold s84_wt
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left htT hlam))
      (Real.rpow_nonneg ht.le _)
  have hKΦ : 0 ≤ K * Φ := mul_nonneg hK0 hΦ0
  have hkey : K * Φ * s84_wt lam t 0 ≤ K * Real.exp (lam * T) * Φ * t ^ (-(3 / 4 : ℝ)) := by
    calc K * Φ * s84_wt lam t 0 ≤ K * Φ * (Real.exp (lam * T) * t ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left hw hKΦ
      _ = _ := by ring
  refine ⟨fun y => (h1 y).trans ?_, fun x x' hx => (h2 x x' hx).trans ?_⟩
  · have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    exact mul_le_mul_of_nonneg_right hkey hj
  · have hj := Real.rpow_nonneg (s83_jb_pos x).le M
    have hS := Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hS) hj

end HRS.MS.Wad
