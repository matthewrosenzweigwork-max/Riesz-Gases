import HRS.MS.WadAux29

/-!
# S8.3, packet D5^9 (Route A): zero-order bound and the a priori estimate

`s84_apriori`: there is `K` (depending on `d, M, a, ν, T, ρ` only) such that every classical solution
`w` (`S84Sol`) on `[0,t]`, `t ≤ T`, satisfies `|w_r(y)| ≤ K Φ ⟨y⟩^M` for `r ∈ [0,t]`, where `Φ` is the
weighted size of the terminal datum `w_t`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_int_t_sub {r t : ℝ} (hrt : r ≤ t) :
    ∫ s in r..t, (t - s) ^ (-(3 / 4 : ℝ)) = 4 * (t - r) ^ (1 / 4 : ℝ) := by
  have := intervalIntegral.integral_comp_sub_left (a := r) (b := t)
    (fun u : ℝ => u ^ (-(3 / 4 : ℝ))) t
  simp only [sub_self] at this
  rw [this, s84_int_rpow]

theorem s84_zero_bound {a ν T M Φ lam t r : ℝ} {ρ : Euc d → ℝ} {w : ℝ → Euc d → ℝ} {CB Θ : ℝ}
    (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) (htT : t ≤ T)
    (hCB : ∀ {h : Euc d → ℝ} {V H : ℝ}, 0 ≤ V → 0 ≤ H →
      (∀ y, ‖fderiv ℝ h y‖ ≤ V * jbracket y ^ M) →
      (∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ h x' - fderiv ℝ h x‖ ≤ H * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M) →
      ∀ x, |s84_Bop ρ h x| ≤ CB * (V + H) * jbracket x ^ M)
    (hCB0 : 0 ≤ CB) (sol : S84Sol ρ a ν t M Φ w) (hΘ : 0 ≤ Θ) (hlam : 0 ≤ lam)
    (hadm : S84Adm lam t M w Θ) (hr : r ∈ Set.Ico 0 t) (y : Euc d) :
    |w r y| ≤ (2 ^ M * mom d M (Real.sqrt (ν / a))) * jbracket y ^ M *
      (Φ + 2 * CB * Θ * (4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ))) := by
  have hr0 : 0 ≤ r := hr.1
  have hrt : r < t := hr.2
  have hrIcc : r ∈ Set.Icc 0 t := ⟨hr.1, hr.2.le⟩
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  set KP : ℝ := 2 ^ M * mom d M (Real.sqrt (ν / a)) with hKP
  have hKP0 : 0 ≤ KP := mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  set τ : ℝ := t - r with hτ
  have hτ0 : 0 < τ := sub_pos.2 hrt
  have hτT : τ ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
  have hqcont : ∀ s ∈ Set.Icc 0 t, Continuous (fun y => s84_Bop ρ (w s) y) := fun s hs =>
    s84_sol_qcont sol hs
  have hqwt : ∀ s ∈ Set.Ioo r t, Wt M (2 * CB * Θ * s84_wt lam t s) (fun y => s84_Bop ρ (w s) y) :=
    fun s hs => s84_q_wt hCB hΘ hadm ⟨hr0.trans hs.1.le, hs.2⟩
  -- the data term
  have hdata : |s83_P a ν τ (w t) y| ≤ Φ * KP * jbracket y ^ M := by
    have := s83_P_wt sol.term_cont hM sol.term_wt ha hν.le hτ0.le y
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [hKP]; ring
  -- the source term
  set g : ℝ → ℝ := fun s => (2 * CB * Θ * KP * jbracket y ^ M * Real.exp (lam * T)) *
    (t - s) ^ (-(3 / 4 : ℝ)) with hg
  have hgi : IntervalIntegrable g volume r t := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - r) (r := -(3 / 4 : ℝ))
      (by norm_num)).comp_sub_left t
    have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume r t := by
      simpa using this.symm
    exact h2.const_mul _
  have hsrc : ‖∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) y‖ ≤
      ∫ s in r..t, g s := by
    refine intervalIntegral.norm_integral_le_of_norm_le hrt.le ?_ hgi
    filter_upwards [(Set.countable_singleton t).ae_notMem (volume : Measure ℝ)] with s hst hs
    have hs' : s ∈ Set.Ioo r t := ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    have hs0 : 0 < s - r := sub_pos.2 hs'.1
    have hw0 := s84_wt_nonneg lam t s hs'.2.le
    have hP := s83_P_wt (hqcont s ⟨hr0.trans hs'.1.le, hs'.2.le⟩) hM (hqwt s hs') ha hν.le hs0.le y
    rw [Real.norm_eq_abs] at hP ⊢
    refine hP.trans ?_
    have hexp : Real.exp (lam * (t - s)) ≤ Real.exp (lam * T) := by
      apply Real.exp_le_exp.2
      exact mul_le_mul_of_nonneg_left (by linarith [hs'.1]) hlam
    have hts : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg (by linarith [hs'.2]) _
    have h0 : 0 ≤ 2 * CB * Θ * KP * jbracket y ^ M := by positivity
    calc 2 * CB * Θ * s84_wt lam t s * 2 ^ M * mom d M (Real.sqrt (ν / a)) * jbracket y ^ M
        = (2 * CB * Θ * KP * jbracket y ^ M) * (Real.exp (lam * (t - s)) * (t - s) ^ (-(3 / 4 : ℝ))) := by
          rw [hKP, s84_wt]; ring
      _ ≤ (2 * CB * Θ * KP * jbracket y ^ M) * (Real.exp (lam * T) * (t - s) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hts) h0
      _ = g s := by rw [hg]; ring
  have hgint : ∫ s in r..t, g s ≤ (2 * CB * Θ * KP * jbracket y ^ M * Real.exp (lam * T)) *
      (4 * T ^ (1 / 4 : ℝ)) := by
    rw [hg, intervalIntegral.integral_const_mul, s84_int_t_sub hrt.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hτ0.le hτT (by norm_num)) (by norm_num)
  rw [sol.mild r hrIcc y]
  refine (abs_add_le _ _).trans ?_
  rw [← Real.norm_eq_abs (∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) y)]
  calc |s83_P a ν τ (w t) y| + ‖∫ s in r..t, s83_P a ν (s - r) (fun y => s84_Bop ρ (w s) y) y‖
      ≤ Φ * KP * jbracket y ^ M + (2 * CB * Θ * KP * jbracket y ^ M * Real.exp (lam * T)) *
        (4 * T ^ (1 / 4 : ℝ)) := add_le_add hdata (hsrc.trans hgint)
    _ = _ := by ring

/-- **The a priori estimate.** -/
theorem s84_apriori (hd : 2 ≤ d) {a ν T M : ℝ} (ha : 0 < a) (hν : 0 < ν) (hT : 0 < T) (hM : 0 ≤ M)
    {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {t Φ : ℝ} {w : ℝ → Euc d → ℝ}, 0 < t → t ≤ T → S84Sol ρ a ν t M Φ w →
      ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, |w r y| ≤ K * Φ * jbracket y ^ M := by
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
  set KP : ℝ := 2 ^ M * mom d M (Real.sqrt (ν / a)) with hKP
  have hKP0 : 0 ≤ KP := mul_nonneg (by positivity) (s83_mom_nonneg _ _ (Real.sqrt_nonneg _))
  refine ⟨max 1 (KP * (1 + 2 * CB * (2 * (3 ^ M * Kst)) * (4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ)))),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro t Φ w ht htT sol r hr y
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  have hjy : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s83_one_le_jb y) hM
  have hjy0 : 0 ≤ jbracket y ^ M := le_trans zero_le_one hjy
  rcases hr.2.eq_or_lt with hrt | hrt
  · -- `r = t`: the terminal datum
    subst hrt
    have := sol.term_wt y
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have h1 : Φ * jbracket y ^ M ≤ max 1 (KP * (1 + 2 * CB * (2 * (3 ^ M * Kst)) *
        (4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ)))) * Φ * jbracket y ^ M := by
      have := le_max_left 1 (KP * (1 + 2 * CB * (2 * (3 ^ M * Kst)) *
        (4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ))))
      nlinarith [mul_nonneg hΦ0 hjy0]
    linarith [h1]
  · have hrI : r ∈ Set.Ico 0 t := ⟨hr.1, hrt⟩
    -- admissibility
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
    have hz := s84_zero_bound ha hν hM htT hCB hCB0 sol (by positivity) hlam0.le hfix hrI y
    refine hz.trans ?_
    set E : ℝ := 4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ) with hE
    have hE0 : 0 ≤ E := by positivity
    have hmax := le_max_right 1 (KP * (1 + 2 * CB * (2 * (3 ^ M * Kst)) * E))
    calc KP * jbracket y ^ M * (Φ + 2 * CB * (2 * (3 ^ M * Kst * Φ)) * E)
        = (KP * (1 + 2 * CB * (2 * (3 ^ M * Kst)) * E)) * Φ * jbracket y ^ M := by ring
      _ ≤ max 1 (KP * (1 + 2 * CB * (2 * (3 ^ M * Kst)) * E)) * Φ * jbracket y ^ M := by
          have := mul_nonneg hΦ0 hjy0
          nlinarith

end HRS.MS.Wad
