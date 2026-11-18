import HRS.MS.WadAux52

/-!
# S8.3, packet S8D-1, part 3: gradient differences of classical solutions, `C¹` structure of `U_t φ`

`s8d_adm_sol`: the time-`0` gradient/Hölder bounds for any `S84Sol`.
`s8d_adm_classical_sub`: the same for the difference of two frozen classical solutions (Lipschitz in the datum).
`s8d_Ucc_C1`: `U_t φ = w_0 + const` is `C¹` with `D U_t φ = D w_0`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_adm_sol (hd : 2 ≤ d) {a ν T M : ℝ} (ha : 0 < a) (hν : 0 < ν) (hT : 0 < T) (hM : 0 ≤ M)
    {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {w : ℝ → Euc d → ℝ}, 0 < t → t ≤ T → S84Sol ρ a ν t M Φ w →
      (∀ y, ‖fderiv ℝ (w 0) y‖ ≤ K * Φ * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M) ∧
      ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ (w 0) x' - fderiv ℝ (w 0) x‖ ≤
          K * Φ * t ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
  obtain ⟨lam, K, hlam, hK0, hK⟩ := s8d_apriori_adm hd ha hν hT hM hρ
  refine ⟨K * Real.exp (lam * T), by positivity, ?_⟩
  intro t Φ w ht htT sol
  have hadm := hK ht htT sol
  obtain ⟨h1, h2⟩ := hadm 0 ⟨le_rfl, ht⟩
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
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

theorem s8d_adm_classical_sub (hd : 2 ≤ d) {a β T M : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM : 0 ≤ M)
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ₁ Φ₂ Φ : ℝ} {φ₁ φ₂ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ}, 0 < t → t ≤ T →
      IsClassicalAdjointW (critCoeff d a β ρβ) t φ₁ f₁ → IsClassicalAdjointW (critCoeff d a β ρβ) t φ₂ f₂ →
      Wt M Φ₁ φ₁ → Wt M Φ₂ φ₂ → Wt M Φ (fun y => φ₁ y - φ₂ y) →
      (∀ y, ‖fderiv ℝ (f₁ 0) y - fderiv ℝ (f₂ 0) y‖ ≤ K * Φ * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M) ∧
      ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖(fderiv ℝ (f₁ 0) x' - fderiv ℝ (f₂ 0) x') - (fderiv ℝ (f₁ 0) x - fderiv ℝ (f₂ 0) x)‖ ≤
          K * Φ * t ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
  have hν : 0 < β⁻¹ := inv_pos.2 hβ
  have hg := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨K, hK0, hK⟩ := s8d_adm_sol hd ha hν hT hM hg
  refine ⟨K, hK0, ?_⟩
  intro t Φ₁ Φ₂ Φ φ₁ φ₂ f₁ f₂ ht htT hf₁ hf₂ hφ₁ hφ₂ hΦ
  have sol₁ := s84_sol_of_classical a β ha hβ ρβ ht hf₁ hφ₁
  have sol₂ := s84_sol_of_classical a β ha hβ ρβ ht hf₂ hφ₂
  have hΦ' : Wt M Φ (fun y => f₁ t y - f₂ t y) := by
    rw [hf₁.terminal, hf₂.terminal]; exact hΦ
  have sol := s84_sol_sub hd ha hν hg hM ht sol₁ sol₂ hΦ'
  obtain ⟨h1, h2⟩ := hK ht htT sol
  have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
  have d1 : Differentiable ℝ (f₁ 0) := (hf₁.c2 0 h0I).differentiable (by norm_num)
  have d2 : Differentiable ℝ (f₂ 0) := (hf₂.c2 0 h0I).differentiable (by norm_num)
  have e1 : fderiv ℝ (fun y => f₁ 0 y - f₂ 0 y) = fun y => fderiv ℝ (f₁ 0) y - fderiv ℝ (f₂ 0) y := by
    funext y; exact fderiv_sub (d1 y) (d2 y)
  have h1' : ∀ y, ‖fderiv ℝ (fun y => f₁ 0 y - f₂ 0 y) y‖ ≤ K * Φ * t ^ (-(3 / 4 : ℝ)) * jbracket y ^ M := h1
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · have := h1' y
    rwa [e1] at this
  · have := h2 x x' hx
    simp only [e1] at this
    exact this

theorem s8d_Ucc_eq_add (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {w : ℝ → Euc d → ℝ} (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) :
    ∃ c : ℝ, s85_Ucc a β ρβ t φ = fun x => w 0 x + c := by
  refine ⟨-(∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)) +
    HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ, ?_⟩
  funext x
  rw [s85_Ucc_eq hd ha hβ hρ ht hw x]
  unfold s85_V
  ring

theorem s8d_Ucc_C1 (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {w : ℝ → Euc d → ℝ} (hw : IsClassicalAdjointW (critCoeff d a β ρβ) t φ w) :
    ContDiff ℝ 1 (s85_Ucc a β ρβ t φ) ∧ ∀ y, fderiv ℝ (s85_Ucc a β ρβ t φ) y = fderiv ℝ (w 0) y := by
  obtain ⟨c, hc⟩ := s8d_Ucc_eq_add hd ha hβ hρ ht hw
  have h2 : ContDiff ℝ 2 (w 0) := hw.c2 0 ⟨le_rfl, ht⟩
  rw [hc]
  refine ⟨(h2.of_le (by norm_num)).add contDiff_const, fun y => ?_⟩
  exact fderiv_add_const c

end HRS.MS.Wad
