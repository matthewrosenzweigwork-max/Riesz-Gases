import HRS.MS.WadAux74

/-!
# S8.3, packet S8E-1, part 4: the Gronwall step and zero-order bound with an abstract source
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- A classical solution (bounded first and second derivatives) is admissible for some `Θ₀`. -/
theorem s8e_adm_start {q : ℝ → Euc d → ℝ} {a ν t M Φ T lam : ℝ} {w : ℝ → Euc d → ℝ}
    (sol : S8eSol q a ν t M Φ w) (hM : 0 ≤ M) (ht : 0 < t) (htT : t ≤ T) (hlam : 0 ≤ lam) :
    ∃ Θ₀ : ℝ, 0 ≤ Θ₀ ∧ S84Adm lam t M w Θ₀ := by
  obtain ⟨B1, B2, hB⟩ := sol.bdd
  have h00 : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht.le⟩
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans ((hB 0 h00 0).1)
  have hB2 : 0 ≤ B2 := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ (w 0)) 0)) (hB 0 h00 0).2
  have hT : 0 < T := ht.trans_le htT
  refine ⟨max B1 B2 * T ^ (3 / 4 : ℝ), by positivity, fun s hs => ?_⟩
  have hsI : s ∈ Set.Icc 0 t := ⟨hs.1, hs.2.le⟩
  set τ : ℝ := t - s with hτ
  have hτ0 : 0 < τ := sub_pos.2 hs.2
  have hτT : τ ≤ T := by linarith [hs.1]
  have hwt : T ^ (-(3 / 4 : ℝ)) ≤ s84_wt lam t s := by
    have h1 : T ^ (-(3 / 4 : ℝ)) ≤ τ ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hτ0 hτT (by norm_num)
    have h2 : 1 ≤ Real.exp (lam * τ) := Real.one_le_exp (by positivity)
    have h3 : 0 < τ ^ (-(3 / 4 : ℝ)) := Real.rpow_pos_of_pos hτ0 _
    unfold s84_wt
    nlinarith
  have hone : T ^ (3 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hT]; simp
  have hmax : max B1 B2 ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s := by
    have hm0 : 0 ≤ max B1 B2 := le_max_of_le_left hB1
    calc max B1 B2 = max B1 B2 * (T ^ (3 / 4 : ℝ) * T ^ (-(3 / 4 : ℝ))) := by rw [hone, mul_one]
      _ ≤ max B1 B2 * (T ^ (3 / 4 : ℝ) * s84_wt lam t s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwt (by positivity)) hm0
      _ = _ := by ring
  have hjb : ∀ y : Euc d, 1 ≤ jbracket y ^ M := fun y => Real.one_le_rpow (s83_one_le_jb y) hM
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · calc ‖fderiv ℝ (w s) y‖ ≤ B1 := (hB s hsI y).1
      _ ≤ max B1 B2 := le_max_left _ _
      _ ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s := hmax
      _ ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s * jbracket y ^ M := by
          have h0 : 0 ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s :=
            le_trans (le_max_of_le_left hB1) hmax
          nlinarith [hjb y]
  · have hd1 : Differentiable ℝ (fderiv ℝ (w s)) :=
      ((sol.c2 s hsI).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have hmv := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := fderiv ℝ (w s)) (C := B2) (fun y _ => hd1 y) (fun y _ => (hB s hsI y).2)
      (Set.mem_univ x) (Set.mem_univ x')
    have hh := s84_norm_le_sqrt hx
    have hS0 : 0 ≤ ‖x' - x‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
    have h0 : 0 ≤ max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s := le_trans (le_max_of_le_left hB1) hmax
    calc ‖fderiv ℝ (w s) x' - fderiv ℝ (w s) x‖ ≤ B2 * ‖x' - x‖ := hmv
      _ ≤ B2 * (‖x' - x‖ ^ (1 / 2 : ℝ) / 2) := mul_le_mul_of_nonneg_left hh hB2
      _ ≤ max B1 B2 * ‖x' - x‖ ^ (1 / 2 : ℝ) := by
          have := le_max_right B1 B2
          nlinarith [mul_nonneg hS0 (sub_nonneg.2 this), mul_nonneg hS0 hB2]
      _ ≤ (max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s) * ‖x' - x‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hmax hS0
      _ ≤ (max B1 B2 * T ^ (3 / 4 : ℝ) * s84_wt lam t s) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
          have := mul_nonneg h0 hS0
          nlinarith [hjb x]

/-- One step of the Gronwall iteration. -/
theorem s8e_step {a ν T M Φ lam εk t K₂ : ℝ} {q : ℝ → Euc d → ℝ} {w : ℝ → Euc d → ℝ} {cB Ex Θ : ℝ}
    (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) (htT : t ≤ T) (hK₂0 : 0 ≤ K₂)
    (hK₂ : ∀ {C : ℝ} {g : Euc d → ℝ}, Continuous g → Wt M C g → ∀ {τ : ℝ}, 0 < τ → τ ≤ T →
      ∀ {x x' : Euc d}, ‖x' - x‖ ≤ 1 / 4 →
      ‖fderiv ℝ (s83_P a ν τ g) x' - fderiv ℝ (s83_P a ν τ g) x‖ ≤
        K₂ * C * τ ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M)
    (hcB : 0 ≤ cB) (hEx : 0 ≤ Ex) (sol : S8eSol q a ν t M Φ w) (hΘ : 0 ≤ Θ) (hlam : 0 ≤ lam) (hεk : 0 ≤ εk)
    (hq : ∀ s ∈ Set.Ico 0 t, Wt M ((cB * Θ + Ex) * s84_wt lam t s) (q s))
    (hker : ∀ r : ℝ, 0 ≤ r → r < t → (∫ s in r..t, (s - r) ^ (-(3 / 4 : ℝ)) *
        ((t - s) ^ (-(3 / 4 : ℝ)) * Real.exp (lam * (t - s)))) ≤
      εk * (Real.exp (lam * (t - r)) * (t - r) ^ (-(3 / 4 : ℝ))))
    (hadm : S84Adm lam t M w Θ) :
    S84Adm lam t M w (3 ^ M * (s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂) * (Φ + (cB * Θ + Ex) * εk)) := by
  intro r hr
  have hw0 := s84_wt_nonneg lam t r hr.2.le
  have hK₁0 : 0 ≤ s84_K1 d M a ν T := s84_K1_nonneg M ha hν
  have hΦ0 : 0 ≤ Φ := sol.term_wt.nonneg
  have hT0 : 0 ≤ T ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith [hr.1, hr.2]) _
  have hQ0 : 0 ≤ Φ + (cB * Θ + Ex) * εk := by positivity
  refine ⟨fun y => ?_, fun x x' hx => ?_⟩
  · refine (s8e_step_sup ha hν hM htT hcB hEx sol hΘ hlam hεk hq hadm hr (hker r hr.1 hr.2) y).trans ?_
    have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    have : s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) ≤ s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂ := by linarith
    calc 3 ^ M * jbracket y ^ M * s84_wt lam t r * (s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) * (Φ + (cB * Θ + Ex) * εk))
        ≤ 3 ^ M * jbracket y ^ M * s84_wt lam t r *
            ((s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂) * (Φ + (cB * Θ + Ex) * εk)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hQ0) (by positivity)
      _ = _ := by ring
  · refine (s8e_step_holder ha hν hM htT hK₂0 hK₂ hcB hEx sol hΘ hlam hεk hq hadm hr (hker r hr.1 hr.2)
      x x' hx).trans ?_
    have hj := Real.rpow_nonneg (s83_jb_pos x).le M
    have hS := Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)
    have : K₂ ≤ s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂ := by
      have := mul_nonneg hK₁0 hT0
      linarith
    calc 3 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) * s84_wt lam t r * (K₂ * (Φ + (cB * Θ + Ex) * εk))
        ≤ 3 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) * s84_wt lam t r *
            ((s84_K1 d M a ν T * T ^ (1 / 4 : ℝ) + K₂) * (Φ + (cB * Θ + Ex) * εk)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hQ0) (by positivity)
      _ = _ := by ring

theorem s8e_zero_bound {a ν T M Φ lam t r : ℝ} {q : ℝ → Euc d → ℝ} {w : ℝ → Euc d → ℝ} {cB Ex Θ : ℝ}
    (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) (htT : t ≤ T)
    (hcB : 0 ≤ cB) (hEx : 0 ≤ Ex) (sol : S8eSol q a ν t M Φ w) (hΘ : 0 ≤ Θ) (hlam : 0 ≤ lam)
    (hq : ∀ s ∈ Set.Ico 0 t, Wt M ((cB * Θ + Ex) * s84_wt lam t s) (q s))
    (hadm : S84Adm lam t M w Θ) (hr : r ∈ Set.Ico 0 t) (y : Euc d) :
    |w r y| ≤ (2 ^ M * mom d M (Real.sqrt (ν / a))) * jbracket y ^ M *
      (Φ + (cB * Θ + Ex) * (4 * Real.exp (lam * T) * T ^ (1 / 4 : ℝ))) := by
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
  have hqcont : ∀ s ∈ Set.Icc 0 t, Continuous (q s) := fun s hs =>
    s8e_qcont sol hs
  have hqwt : ∀ s ∈ Set.Ioo r t, Wt M ((cB * Θ + Ex) * s84_wt lam t s) (q s) :=
    fun s hs => hq s ⟨hr0.trans hs.1.le, hs.2⟩
  -- the data term
  have hdata : |s83_P a ν τ (w t) y| ≤ Φ * KP * jbracket y ^ M := by
    have := s83_P_wt sol.term_cont hM sol.term_wt ha hν.le hτ0.le y
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [hKP]; ring
  -- the source term
  set g : ℝ → ℝ := fun s => ((cB * Θ + Ex) * KP * jbracket y ^ M * Real.exp (lam * T)) *
    (t - s) ^ (-(3 / 4 : ℝ)) with hg
  have hgi : IntervalIntegrable g volume r t := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - r) (r := -(3 / 4 : ℝ))
      (by norm_num)).comp_sub_left t
    have h2 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume r t := by
      simpa using this.symm
    exact h2.const_mul _
  have hsrc : ‖∫ s in r..t, s83_P a ν (s - r) (q s) y‖ ≤
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
    have h0 : 0 ≤ (cB * Θ + Ex) * KP * jbracket y ^ M := by positivity
    calc (cB * Θ + Ex) * s84_wt lam t s * 2 ^ M * mom d M (Real.sqrt (ν / a)) * jbracket y ^ M
        = ((cB * Θ + Ex) * KP * jbracket y ^ M) * (Real.exp (lam * (t - s)) * (t - s) ^ (-(3 / 4 : ℝ))) := by
          rw [hKP, s84_wt]; ring
      _ ≤ ((cB * Θ + Ex) * KP * jbracket y ^ M) * (Real.exp (lam * T) * (t - s) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hts) h0
      _ = g s := by rw [hg]; ring
  have hgint : ∫ s in r..t, g s ≤ ((cB * Θ + Ex) * KP * jbracket y ^ M * Real.exp (lam * T)) *
      (4 * T ^ (1 / 4 : ℝ)) := by
    rw [hg, intervalIntegral.integral_const_mul, s84_int_t_sub hrt.le]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hτ0.le hτT (by norm_num)) (by norm_num)
  rw [sol.mild r hrIcc y]
  refine (abs_add_le _ _).trans ?_
  rw [← Real.norm_eq_abs (∫ s in r..t, s83_P a ν (s - r) (q s) y)]
  calc |s83_P a ν τ (w t) y| + ‖∫ s in r..t, s83_P a ν (s - r) (q s) y‖
      ≤ Φ * KP * jbracket y ^ M + ((cB * Θ + Ex) * KP * jbracket y ^ M * Real.exp (lam * T)) *
        (4 * T ^ (1 / 4 : ℝ)) := add_le_add hdata (hsrc.trans hgint)
    _ = _ := by ring

end HRS.MS.Wad
