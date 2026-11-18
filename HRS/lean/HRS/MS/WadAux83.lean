import HRS.MS.WadAux82

/-!
# S8.3, packet S8E-3, part 4: the weighted size of the source of a flow-shifted difference

`s8e_thermal_diff`: the difference density `ρβ(·+z) - ρβ` of the thermal density has Gaussian bounds with a constant
proportional to `‖z‖`.  `s8e_qu_wt`: if `w` is a mild solution with admissible constant `Θw` then the source `qu` of the
flow-shifted difference `u` of `w` satisfies the hypothesis of `s8e_apriori_gen`, with `cB = 2 C_B` and
`Ex = Kc Cρ ‖ζ‖ 2 · 3^M Θw e^{λ₀T}`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_thermal_diff (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (h : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ Cρ c : ℝ, 0 ≤ Cρ ∧ 0 < c ∧ ∀ z : Euc d, ‖z‖ ≤ 1 → ∀ x : Euc d,
      |ρ (x + z) - ρ x| ≤ (Cρ * ‖z‖) * Real.exp (-c * ‖x‖ ^ 2) ∧
      ‖fderiv ℝ ρ (x + z) - fderiv ℝ ρ x‖ ≤ (Cρ * ‖z‖) * Real.exp (-c * ‖x‖ ^ 2) := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hsm, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd hs0 hsd ha hβ h
  refine s8e_rho_diff_gauss (ρ := ρ) (hsm.of_le (by simp)) (fun k _ => ?_)
  obtain ⟨C, c, hc, hb⟩ := hg k
  refine ⟨max C 0, c, le_max_right _ _, hc, fun x => (hb x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

theorem s8e_wt_comp {lam lam₀ t s T : ℝ} (hlam : 0 ≤ lam) (hlam₀ : 0 ≤ lam₀) (hs : 0 ≤ s) (hst : s < t)
    (htT : t ≤ T) : s84_wt lam₀ t s ≤ Real.exp (lam₀ * T) * s84_wt lam t s := by
  unfold s84_wt
  have hp : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have h1 : Real.exp (lam₀ * (t - s)) ≤ Real.exp (lam₀ * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hlam₀)
  have h2 : 1 ≤ Real.exp (lam * (t - s)) := Real.one_le_exp (mul_nonneg hlam (by linarith))
  calc Real.exp (lam₀ * (t - s)) * (t - s) ^ (-(3 / 4 : ℝ))
      ≤ Real.exp (lam₀ * T) * (t - s) ^ (-(3 / 4 : ℝ)) := mul_le_mul_of_nonneg_right h1 hp
    _ ≤ Real.exp (lam₀ * T) * (Real.exp (lam * (t - s)) * (t - s) ^ (-(3 / 4 : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        nlinarith
    _ = _ := by ring

theorem s8e_qu_wt (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hg : s84_GaussReg ρ) {M : ℝ} (hM : 0 ≤ M)
    {CB Kc Cρ c' : ℝ}
    (hCB : ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop ρ h x| ≤ CB * (V + H) * jbracket x ^ M)
    (hKc : ∀ {σ : Euc d → ℝ} {C : ℝ}, 0 ≤ C → Differentiable ℝ σ →
      (∀ x, |σ x| ≤ C * Real.exp (-c' * ‖x‖ ^ 2) ∧ ‖fderiv ℝ σ x‖ ≤ C * Real.exp (-c' * ‖x‖ ^ 2)) →
      ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop σ h x| ≤ Kc * C * (V + H) * jbracket x ^ M)
    (hKc0 : 0 ≤ Kc) (hCρ0 : 0 ≤ Cρ)
    (hρd : ∀ z : Euc d, ‖z‖ ≤ 1 → ∀ x : Euc d,
      |ρ (x + z) - ρ x| ≤ (Cρ * ‖z‖) * Real.exp (-c' * ‖x‖ ^ 2) ∧
      ‖fderiv ℝ ρ (x + z) - fderiv ℝ ρ x‖ ≤ (Cρ * ‖z‖) * Real.exp (-c' * ‖x‖ ^ 2))
    {a t lam lam₀ T Θw Θ : ℝ} {f : ℝ → Euc d → ℝ} {B : ℝ} {ζ : Euc d}
    (hC2 : ∀ s ∈ Set.Icc 0 t, s84_C2b (f s) B) (ha : 0 ≤ a) (hζ : ‖ζ‖ < 1 / 8)
    (hadmw : S84Adm lam₀ t M f Θw) (hΘw : 0 ≤ Θw) (htT : t ≤ T) (hlam : 0 ≤ lam) (hlam₀ : 0 ≤ lam₀)
    (hΘ : 0 ≤ Θ) (hadm : S84Adm lam t M (s8e_u a ζ f) Θ) {s : ℝ} (hs : s ∈ Set.Ico 0 t) :
    Wt M ((2 * CB * Θ + Kc * Cρ * ‖ζ‖ * (2 * (3 ^ M * (Θw * Real.exp (lam₀ * T))))) * s84_wt lam t s)
      (fun y => s84_Bop ρ (f s) (y + s8e_zs a ζ s) - s84_Bop ρ (f s) y) := by
  intro y
  set z : Euc d := s8e_zs a ζ s with hz
  have hz0 : ‖z‖ ≤ ‖ζ‖ := s8e_zs_norm ha hs.1 ζ
  have hz8 : ‖z‖ < 1 / 8 := lt_of_le_of_lt hz0 hζ
  have hz1 : ‖z‖ ≤ 1 := by linarith
  have hz4 : ‖z‖ < 1 / 4 := by linarith
  have hsI : s ∈ Set.Icc 0 t := ⟨hs.1, hs.2.le⟩
  have hw0 : 0 ≤ s84_wt lam t s := s84_wt_nonneg lam t s hs.2.le
  have hwc := s8e_wt_comp hlam hlam₀ hs.1 hs.2 htT (T := T)
  have hE0 : 0 < Real.exp (lam₀ * T) := Real.exp_pos _
  set Vw : ℝ := 3 ^ M * (Θw * Real.exp (lam₀ * T)) * s84_wt lam t s with hVw
  have hV0 : 0 ≤ Vw := by positivity
  obtain ⟨hA1, hA2⟩ := hadmw s hs
  have hw00 := s84_wt_nonneg lam₀ t s hs.2.le
  have hVle : Θw * s84_wt lam₀ t s * 3 ^ M ≤ Vw := by
    rw [hVw]
    have := mul_le_mul_of_nonneg_left hwc hΘw
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 3 by norm_num) M]
  set h' : Euc d → ℝ := fun y => f s (y + z) with hh'
  have hfd : ∀ y, fderiv ℝ h' y = fderiv ℝ (f s) (y + z) := fun y => by
    rw [hh', fderiv_comp_add_right]
  have hD : ∀ y, ‖fderiv ℝ h' y‖ ≤ Vw * jbracket y ^ M := fun y => by
    rw [hfd]
    refine (hA1 (y + z)).trans ?_
    calc Θw * s84_wt lam₀ t s * jbracket (y + z) ^ M
        ≤ Θw * s84_wt lam₀ t s * (3 ^ M * jbracket y ^ M) :=
          mul_le_mul_of_nonneg_left (s8e_jb_shift hM hz4 y) (by positivity)
      _ = (Θw * s84_wt lam₀ t s * 3 ^ M) * jbracket y ^ M := by ring
      _ ≤ Vw * jbracket y ^ M := mul_le_mul_of_nonneg_right hVle (Real.rpow_nonneg (s83_jb_pos y).le _)
  have hH : ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
      ‖fderiv ℝ h' x' - fderiv ℝ h' x‖ ≤ Vw * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := fun x x' hx => by
    rw [hfd, hfd]
    have hx' : ‖(x' + z) - (x + z)‖ ≤ 1 / 4 := by rwa [add_sub_add_right_eq_sub]
    have := hA2 (x + z) (x' + z) hx'
    rw [add_sub_add_right_eq_sub] at this
    refine this.trans ?_
    have hS := Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)
    calc Θw * s84_wt lam₀ t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket (x + z) ^ M
        ≤ Θw * s84_wt lam₀ t s * ‖x' - x‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M) :=
          mul_le_mul_of_nonneg_left (s8e_jb_shift hM hz4 x) (by positivity)
      _ = (Θw * s84_wt lam₀ t s * 3 ^ M) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by ring
      _ ≤ Vw * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVle hS)
            (Real.rpow_nonneg (s83_jb_pos x).le _)
  -- the source of the density difference
  have hdiff : Differentiable ℝ (fun y => ρ (y + z) - ρ y) := fun y =>
    ((hg.1 (y + z)).comp y (differentiableAt_id.add_const z)).sub (hg.1 y)
  have hgb : ∀ x, |ρ (x + z) - ρ x| ≤ (Cρ * ‖ζ‖) * Real.exp (-c' * ‖x‖ ^ 2) ∧
      ‖fderiv ℝ (fun y => ρ (y + z) - ρ y) x‖ ≤ (Cρ * ‖ζ‖) * Real.exp (-c' * ‖x‖ ^ 2) := fun x => by
    have hmono : Cρ * ‖z‖ * Real.exp (-c' * ‖x‖ ^ 2) ≤ Cρ * ‖ζ‖ * Real.exp (-c' * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz0 hCρ0) (Real.exp_pos _).le
    obtain ⟨b1, b2⟩ := hρd z hz1 x
    refine ⟨b1.trans hmono, ?_⟩
    rw [(s84_fderiv_shift_sub hg.1 z x).2]
    exact b2.trans hmono
  have hBe := hKc (mul_nonneg hCρ0 (norm_nonneg ζ)) hdiff hgb hV0 hV0 hD hH y
  -- the first-order part
  have hB1 := s84_q_wt (w := s8e_u a ζ f) hCB hΘ hadm hs y
  have hdec := s8e_qu_decomp hd hg (hC2 s hsI) hz1 y
  show ‖s84_Bop ρ (f s) (y + z) - s84_Bop ρ (f s) y‖ ≤ _
  rw [Real.norm_eq_abs, hdec]
  refine (abs_add_le _ _).trans ?_
  rw [Real.norm_eq_abs] at hB1
  have hj := Real.rpow_nonneg (s83_jb_pos y).le M
  have e : Kc * (Cρ * ‖ζ‖) * (Vw + Vw) * jbracket y ^ M =
      (Kc * Cρ * ‖ζ‖ * (2 * (3 ^ M * (Θw * Real.exp (lam₀ * T))))) * s84_wt lam t s * jbracket y ^ M := by
    rw [hVw]; ring
  rw [e] at hBe
  have e2 : (2 * CB * Θ + Kc * Cρ * ‖ζ‖ * (2 * (3 ^ M * (Θw * Real.exp (lam₀ * T))))) * s84_wt lam t s *
      jbracket y ^ M = 2 * CB * Θ * s84_wt lam t s * jbracket y ^ M +
      (Kc * Cρ * ‖ζ‖ * (2 * (3 ^ M * (Θw * Real.exp (lam₀ * T))))) * s84_wt lam t s * jbracket y ^ M := by
    ring
  rw [e2]
  exact add_le_add hB1 hBe

end HRS.MS.Wad
