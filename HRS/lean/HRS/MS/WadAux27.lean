import HRS.MS.WadAux26

/-!
# S8.3, packet D5^6 (Route A): the Hölder step of the a priori estimate

`s84_step_holder`: with the hypotheses of `s84_step_sup`, for `‖x'-x‖ ≤ 1/4`,
`‖Dw_r(x') - Dw_r(x)‖ ≤ 3^M ⟨x⟩^M ‖x'-x‖^{1/2} ρ_λ(r) K₂ (Φ + 2 C_B Θ ε)`.
Proof: the second difference `Ψ(y) = w_r(y+Δ) - w_r(y)` has a mild form whose Lipschitz constant on a ball is
controlled by `s84_P_fderiv_holder` and `s84_lip_mild`; `DΨ(x) = Dw_r(x') - Dw_r(x)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s84_step_holder {a ν T M Φ lam εk t r K₂ : ℝ} {ρ : Euc d → ℝ} {w : ℝ → Euc d → ℝ} {CB Θ : ℝ}
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
    (hadm : S84Adm lam t M w Θ) (hr : r ∈ Set.Ico 0 t)
    (hker : (∫ s in r..t, (s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ)))) (x x' : Euc d)
    (hxx : ‖x' - x‖ ≤ 1 / 4) :
    ‖fderiv ℝ (w r) x' - fderiv ℝ (w r) x‖ ≤
      3 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) * s84_wt lam t r *
        (K₂ * (Φ + 2 * CB * Θ * εk)) := by
  have hr0 : 0 ≤ r := hr.1
  have hrt : r < t := hr.2
  have hrIcc : r ∈ Set.Icc 0 t := ⟨hr.1, hr.2.le⟩
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  set τ : ℝ := t - r with hτ
  have hτ0 : 0 < τ := sub_pos.2 hrt
  have hτT : τ ≤ T := by linarith
  have hjx : 0 < jbracket x := s83_jb_pos x
  set Δ : Euc d := x' - x with hΔ
  have hΔ0 : 0 ≤ ‖Δ‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hP1c : ContDiff ℝ 1 (s83_P a ν τ (w t)) :=
    (s84_P_fderiv (T := T) ha hν hM sol.term_cont sol.term_wt hτ0 hτT).1
  have hqcont : ∀ s ∈ Set.Icc 0 t, Continuous (fun y => s84_Bop ρ (w s) y) := fun s hs =>
    s84_sol_qcont sol hs
  have hqwt : ∀ s ∈ Set.Ioo r t, Wt M (2 * CB * Θ * s84_wt lam t s) (fun y => s84_Bop ρ (w s) y) :=
    fun s hs => s84_q_wt hCB hΘ hadm ⟨hr0.trans hs.1.le, hs.2⟩
  set c₂ : ℝ := K₂ * (2 * CB * Θ) * (‖Δ‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M)) with hc₂
  have hc₂0 : 0 ≤ c₂ := by positivity
  set B0 : ℝ := K₂ * Φ * τ ^ (-(3 / 4 : ℝ)) * (‖Δ‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M)) with hB0
  -- the second difference
  have hlip := s84_lip_mild hrt (convex_ball x (1 / 4))
    (u := fun y => w r (y + Δ) - w r y)
    (d0 := fun y => s83_P a ν τ (w t) (y + Δ) - s83_P a ν τ (w t) y)
    (f := fun s y => s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) (y + Δ) -
      s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) y)
    (B0 := B0) (b := fun s => c₂ * ((s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))))
    (fun y _ => by
      rw [sol.mild r hrIcc (y + Δ), sol.mild r hrIcc y,
        intervalIntegral.integral_sub (s84_hint ha hν sol hrIcc (y + Δ)) (s84_hint ha hν sol hrIcc y)]
      ring)
    (fun y _ => (s84_hint ha hν sol hrIcc (y + Δ)).sub (s84_hint ha hν sol hrIcc y))
    (fun y hy => by
      obtain ⟨h1, h2⟩ := s84_fderiv_shift_sub (hP1c.differentiable one_ne_zero) Δ y
      refine ⟨h1, ?_⟩
      rw [h2]
      have := hK₂ sol.term_cont sol.term_wt hτ0 hτT (x := y) (x' := y + Δ)
        (by rw [add_sub_cancel_left]; exact hxx)
      rw [add_sub_cancel_left] at this
      refine this.trans ?_
      have hjy := s84_jb_ball hM hy
      rw [hB0]
      calc K₂ * Φ * τ ^ (-(3 / 4 : ℝ)) * ‖Δ‖ ^ (1 / 2 : ℝ) * jbracket y ^ M
          ≤ K₂ * Φ * τ ^ (-(3 / 4 : ℝ)) * ‖Δ‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M) :=
            mul_le_mul_of_nonneg_left hjy (by positivity)
        _ = _ := by ring)
    (fun s hs y hy => by
      have hs0 : 0 < s - r := sub_pos.2 hs.1
      have hsT : s - r ≤ T := by linarith [hs.2]
      have hqc := hqcont s ⟨hr0.trans hs.1.le, hs.2.le⟩
      have hf1 := (s84_P_fderiv (T := T) ha hν hM hqc (hqwt s hs) hs0 hsT).1
      obtain ⟨h1, h2⟩ := s84_fderiv_shift_sub (hf1.differentiable one_ne_zero) Δ y
      refine ⟨h1, ?_⟩
      rw [h2]
      have := hK₂ hqc (hqwt s hs) hs0 hsT (x := y) (x' := y + Δ)
        (by rw [add_sub_cancel_left]; exact hxx)
      rw [add_sub_cancel_left] at this
      refine this.trans ?_
      have hjy := s84_jb_ball hM hy
      have hw0 : 0 ≤ s84_wt lam t s := s84_wt_nonneg lam t s hs.2.le
      calc K₂ * (2 * CB * Θ * s84_wt lam t s) * (s - r) ^ (-(3 / 4 : ℝ)) * ‖Δ‖ ^ (1 / 2 : ℝ) * jbracket y ^ M
          ≤ K₂ * (2 * CB * Θ * s84_wt lam t s) * (s - r) ^ (-(3 / 4 : ℝ)) * ‖Δ‖ ^ (1 / 2 : ℝ) *
              (3 ^ M * jbracket x ^ M) := mul_le_mul_of_nonneg_left hjy (by positivity)
        _ = _ := by rw [hc₂, s84_wt]; ring)
    ((s84_kernel_ii hrt).const_mul c₂)
  have hint : (∫ s in r..t, c₂ * ((s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))))) ≤
      c₂ * (εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ)))) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hker hc₂0
  have hwr : s84_wt lam t r = Real.exp (lam * τ) * τ ^ (-(3 / 4 : ℝ)) := rfl
  have hexp1 : 1 ≤ Real.exp (lam * τ) := Real.one_le_exp (by positivity)
  have hτp : 0 < τ ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hτ0 _
  have hwr1 : τ ^ (-(3 / 4 : ℝ)) ≤ s84_wt lam t r := by
    rw [hwr]; nlinarith
  have hwr0 : 0 ≤ s84_wt lam t r := s84_wt_nonneg lam t r hrt.le
  have hfinal : B0 + ∫ s in r..t, c₂ * ((s - r) ^ (-(3 / 4 : ℝ)) *
      ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      3 ^ M * jbracket x ^ M * ‖Δ‖ ^ (1 / 2 : ℝ) * s84_wt lam t r * (K₂ * (Φ + 2 * CB * Θ * εk)) := by
    have h2 : c₂ * (εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ)))) =
        c₂ * εk * s84_wt lam t r := by rw [hwr]; ring
    have hB0le : B0 ≤ K₂ * Φ * s84_wt lam t r * (‖Δ‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M)) := by
      rw [hB0]
      have h0 : 0 ≤ K₂ * Φ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwr1 h0) (by positivity)
    calc B0 + ∫ s in r..t, c₂ * ((s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s))))
        ≤ K₂ * Φ * s84_wt lam t r * (‖Δ‖ ^ (1 / 2 : ℝ) * (3 ^ M * jbracket x ^ M)) +
            c₂ * εk * s84_wt lam t r := by
          rw [← h2]; exact add_le_add hB0le hint
      _ = _ := by rw [hc₂]; ring
  have hBfin : 0 ≤ 3 ^ M * jbracket x ^ M * ‖Δ‖ ^ (1 / 2 : ℝ) * s84_wt lam t r *
      (K₂ * (Φ + 2 * CB * Θ * εk)) := by positivity
  -- derivative of the second difference at `x`
  have hdiffw : Differentiable ℝ (w r) := (sol.c2 r hrIcc).differentiable (by norm_num)
  obtain ⟨hdΨ, hfΨ⟩ := s84_fderiv_shift_sub hdiffw Δ x
  have hxΔ : x + Δ = x' := by rw [hΔ]; abel
  have := s84_fderiv_le_of_lip (u := fun y => w r (y + Δ) - w r y) (x := x) (ε := 1 / 4)
    (by norm_num) hBfin hdΨ
    (fun y hy y' hy' => (hlip y hy y' hy').trans (mul_le_mul_of_nonneg_right hfinal (norm_nonneg _)))
  rw [hfΨ, hxΔ] at this
  exact this

end HRS.MS.Wad
