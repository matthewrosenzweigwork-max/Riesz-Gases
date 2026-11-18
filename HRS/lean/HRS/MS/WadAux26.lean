import HRS.MS.WadAux25

/-!
# S8.3, packet D5^5 (Route A): the sup-bound step of the a priori estimate

`s84_step_sup`: if `Θ` is admissible for `w` and `q = 𝓑 w` then, with the singular kernel inequality
`hker` for `[r,t]`, `‖Dw_r(x)‖ ≤ 3^M ⟨x⟩^M ρ_λ(r) K₁ T^{1/4} (Φ + 2 C_B Θ ε)`.
Proof: mild form + `s84_lip_mild` (Lipschitz bound of `w_r` on a ball) + `s84_P_fderiv`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_inv_sqrt_le {τ T : ℝ} (hτ : 0 < τ) (hτT : τ ≤ T) :
    (Real.sqrt τ)⁻¹ ≤ T ^ (1 / 4 : ℝ) * τ ^ (-(3 / 4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hτ.le]
  have : τ ^ (-(1 / 2 : ℝ)) = τ ^ (1 / 4 : ℝ) * τ ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hτ]; norm_num
  rw [this]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hτ.le hτT (by norm_num)) (Real.rpow_nonneg hτ.le _)

theorem s84_jb_ball {x y : Euc d} {M : ℝ} (hM : 0 ≤ M) (hy : y ∈ ball x (1 / 4)) :
    jbracket y ^ M ≤ 3 ^ M * jbracket x ^ M := by
  rw [mem_ball_iff_norm] at hy
  have h : jbracket y ≤ 3 * jbracket x := s83_jb_le_three (by linarith)
  calc jbracket y ^ M ≤ (3 * jbracket x) ^ M := Real.rpow_le_rpow (s83_jb_pos _).le h hM
    _ = 3 ^ M * jbracket x ^ M := Real.mul_rpow (by norm_num) (s83_jb_pos _).le

theorem s84_sol_qcont {ρ : Euc d → ℝ} {a ν t M Φ : ℝ} {w : ℝ → Euc d → ℝ} (sol : S84Sol ρ a ν t M Φ w)
    {s : ℝ} (hs : s ∈ Set.Icc 0 t) : Continuous (fun y : Euc d => s84_Bop ρ (w s) y) := by
  have h1 := continuousOn_iff_continuous_restrict.1 sol.hqc
  have h2 : Continuous (fun y : Euc d => (⟨(s, y), ⟨hs, Set.mem_univ y⟩⟩ :
      (Set.Icc (0 : ℝ) t ×ˢ (Set.univ : Set (Euc d))))) :=
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) _
  have h3 := h1.comp h2
  simpa [Function.comp_def, Set.restrict] using h3

set_option maxHeartbeats 800000 in
theorem s84_step_sup {a ν T M Φ lam εk t r : ℝ} {ρ : Euc d → ℝ} {w : ℝ → Euc d → ℝ} {CB Θ : ℝ}
    (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) (htT : t ≤ T)
    (hCB : ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop ρ h x| ≤ CB * (V + H) * jbracket x ^ M)
    (hCB0 : 0 ≤ CB) (sol : S84Sol ρ a ν t M Φ w) (hΘ : 0 ≤ Θ) (hlam : 0 ≤ lam) (hεk : 0 ≤ εk)
    (hadm : S84Adm lam t M w Θ) (hr : r ∈ Set.Ico 0 t)
    (hker : (∫ s in r..t, (s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ)))) (x : Euc d) :
    ‖fderiv ℝ (w r) x‖ ≤ 3 ^ M * jbracket x ^ M * s84_wt lam t r *
      (s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) * (Φ + 2 * CB * Θ * εk)) := by
  have hr0 : 0 ≤ r := hr.1
  have hrt : r < t := hr.2
  have hrIcc : r ∈ Set.Icc 0 t := ⟨hr.1, hr.2.le⟩
  set K₁ : ℝ := s84_K1 d M a ν T with hK₁
  have hK₁0 : 0 ≤ K₁ := s84_K1_nonneg M ha hν
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  set τ : ℝ := t - r with hτ
  have hτ0 : 0 < τ := sub_pos.2 hrt
  have hτT : τ ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hjx : 0 < jbracket x := s83_jb_pos x
  obtain ⟨hP1c, hP1⟩ := s84_P_fderiv (T := T) ha hν hM sol.term_cont sol.term_wt hτ0 hτT
  have hqcont : ∀ s ∈ Set.Icc 0 t, Continuous (fun y => s84_Bop ρ (w s) y) := fun s hs =>
    s84_sol_qcont sol hs
  have hqwt : ∀ s ∈ Set.Ioo r t, Wt M (2 * CB * Θ * s84_wt lam t s) (fun y => s84_Bop ρ (w s) y) :=
    fun s hs => s84_q_wt hCB hΘ hadm ⟨hr0.trans hs.1.le, hs.2⟩
  set c₁ : ℝ := K₁ * T ^ (1 / 4 : ℝ) * (2 * CB * Θ) * (3 ^ M * jbracket x ^ M) with hc₁
  have hc₁0 : 0 ≤ c₁ := by positivity
  set B0 : ℝ := K₁ * Φ * (Real.sqrt τ)⁻¹ * (3 ^ M * jbracket x ^ M) with hB0
  have hlip := s84_lip_mild hrt (convex_ball x (1 / 4)) (u := w r)
    (d0 := s83_P a ν τ (w t)) (f := fun s => s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y))
    (B0 := B0) (b := fun s => c₁ * ((s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))))
    (fun y _ => sol.mild r hrIcc y) (fun y _ => s84_hint ha hν sol hrIcc y)
    (fun y hy => ⟨(hP1c.differentiable one_ne_zero) y, (hP1 y).trans (by
      rw [hB0]
      have := s84_jb_ball hM hy
      have h0 : 0 ≤ K₁ * Φ * (Real.sqrt τ)⁻¹ := by positivity
      calc K₁ * Φ * (Real.sqrt τ)⁻¹ * jbracket y ^ M ≤ K₁ * Φ * (Real.sqrt τ)⁻¹ * (3 ^ M * jbracket x ^ M) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring)⟩)
    (fun s hs y hy => by
      have hs0 : 0 < s - r := sub_pos.2 hs.1
      have hsT : s - r ≤ T := by linarith [hs.2]
      obtain ⟨hf1, hf2⟩ := s84_P_fderiv (T := T) ha hν hM (hqcont s ⟨hr0.trans hs.1.le, hs.2.le⟩)
        (hqwt s hs) hs0 hsT
      refine ⟨(hf1.differentiable one_ne_zero) y, (hf2 y).trans ?_⟩
      have hjy := s84_jb_ball hM hy
      have hinv := s84_inv_sqrt_le hs0 hsT
      have hw0 : 0 ≤ s84_wt lam t s := s84_wt_nonneg lam t s hs.2.le
      have h0 : 0 ≤ K₁ * (2 * CB * Θ * s84_wt lam t s) := by positivity
      calc K₁ * (2 * CB * Θ * s84_wt lam t s) * (Real.sqrt (s - r))⁻¹ * jbracket y ^ M
          ≤ K₁ * (2 * CB * Θ * s84_wt lam t s) * (T ^ (1 / 4 : ℝ) * (s - r) ^ (-(3 / 4 : ℝ))) *
              (3 ^ M * jbracket x ^ M) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hinv h0) hjy (Real.rpow_nonneg (s83_jb_pos _).le _)
              (mul_nonneg h0 (mul_nonneg (Real.rpow_nonneg hT0.le _) (Real.rpow_nonneg hs0.le _)))
        _ = _ := by rw [hc₁, s84_wt]; ring)
    ((s84_kernel_ii hrt).const_mul c₁)
  -- evaluate the bound
  have hint : (∫ s in r..t, c₁ * ((s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))))) ≤
      c₁ * (εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ)))) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hker hc₁0
  have hwr : s84_wt lam t r = Real.exp (lam * τ) * τ ^ (-(3 / 4 : ℝ)) := rfl
  have hexp1 : 1 ≤ Real.exp (lam * τ) := Real.one_le_exp (by positivity)
  have hτp : 0 < τ ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hτ0 _
  have hwr1 : τ ^ (-(3 / 4 : ℝ)) ≤ s84_wt lam t r := by
    rw [hwr]; nlinarith
  have hinv := s84_inv_sqrt_le hτ0 hτT
  have hB0le : B0 ≤ K₁ * Φ * T ^ (1 / 4 : ℝ) * s84_wt lam t r * (3 ^ M * jbracket x ^ M) := by
    rw [hB0]
    have h0 : 0 ≤ K₁ * Φ := by positivity
    have : (Real.sqrt τ)⁻¹ ≤ T ^ (1 / 4 : ℝ) * s84_wt lam t r :=
      hinv.trans (mul_le_mul_of_nonneg_left hwr1 (by positivity))
    calc K₁ * Φ * (Real.sqrt τ)⁻¹ * (3 ^ M * jbracket x ^ M)
        ≤ K₁ * Φ * (T ^ (1 / 4 : ℝ) * s84_wt lam t r) * (3 ^ M * jbracket x ^ M) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) (by positivity)
      _ = _ := by ring
  have hfinal : B0 + ∫ s in r..t, c₁ * ((s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      3 ^ M * jbracket x ^ M * s84_wt lam t r * (K₁ * T ^ (1 / 4 : ℝ) * (Φ + 2 * CB * Θ * εk)) := by
    have hwr0 : 0 ≤ s84_wt lam t r := s84_wt_nonneg lam t r hrt.le
    have h2 : c₁ * (εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ)))) =
        c₁ * εk * s84_wt lam t r := by rw [hwr]; ring
    calc B0 + ∫ s in r..t, c₁ * ((s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))))
        ≤ K₁ * Φ * T ^ (1 / 4 : ℝ) * s84_wt lam t r * (3 ^ M * jbracket x ^ M) +
            c₁ * εk * s84_wt lam t r := by
          rw [← h2]; exact add_le_add hB0le hint
      _ = _ := by rw [hc₁]; ring
  have hBfin : 0 ≤ 3 ^ M * jbracket x ^ M * s84_wt lam t r *
      (K₁ * T ^ (1 / 4 : ℝ) * (Φ + 2 * CB * Θ * εk)) := by
    have hwr0 : 0 ≤ s84_wt lam t r := s84_wt_nonneg lam t r hrt.le
    positivity
  exact s84_fderiv_le_of_lip (u := w r) (x := x) (ε := 1 / 4) (by norm_num) hBfin
    ((sol.c2 r hrIcc).differentiable (by norm_num) x)
    (fun y hy y' hy' => (hlip y hy y' hy').trans (mul_le_mul_of_nonneg_right hfinal (norm_nonneg _)))

end HRS.MS.Wad
